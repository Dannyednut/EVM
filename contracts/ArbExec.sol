// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

import "./interfaces/IUniswapV2Pair.sol";
import "./interfaces/IUniswapV3Pool.sol";
import "./interfaces/IQuoter.sol";
import "./interfaces/IWETH.sol";
import "./interfaces/IAavePool.sol";
import "./interfaces/IBalancerVault.sol";
import {Helper} from "./libraries/Helper.sol";

struct ArbData {
    address[] tokens;
    address[] pools;
    uint256 amountIn;
    address tokenIn;
    address borrowPool;
    uint24[] fees;
    uint256 minProfit;
    uint8 mode; // 0 = borrow token in, 1 = borrow other token
}

struct V2CB {
    ArbData arb;
    uint256 borrowed;
    address debtToken;
    uint256 debtAmount;
    uint256 startBalance;
}

contract ArbExec is Ownable, ReentrancyGuard {
    using SafeERC20 for IERC20;

    address public immutable WETH;
    address public immutable Quoter;
    address public immutable AAVE_POOL;
    address public immutable BALANCER_VAULT;

    // Set before initiating any flash loan/swap, validated inside every callback,
    // and cleared immediately after validation to prevent re-use.
    address private _expectedCallback;

    event FLA(address indexed t, uint256 a);
    event FSV2(address indexed p, uint256 a);
    event FSV3(address indexed p, uint256 a);
    event DONE(address indexed profitToken, uint256 amt);

    /// @notice Deploys the contract and sets immutable protocol addresses.
    /// @param _w  WETH token address used for unwrapping profits.
    /// @param _q  View-only Quoter address for simulating V3 swap outputs.
    /// @param _a  Aave V3 lending pool address, or address(0) to disable Aave flash loans.
    /// @param _b  Balancer Vault address, or address(0) to disable Balancer flash loans.
    constructor(address _w, address _q, address _a, address _b) Ownable(msg.sender) {
        require(_w != address(0), "zero WETH");
        require(_q != address(0), "zero Quoter");
        WETH = _w;
        Quoter = _q;
        AAVE_POOL = _a;
        BALANCER_VAULT = _b;
    }

    /// @dev Accepts ETH from WETH.withdraw() during profit unwrapping.
    receive() external payable {}

    /// @dev Redirects non-standard V2 fork swap callbacks (e.g. pancakeV2Call, sushiCall)
    ///      to uniswapV2Call. Any 4-byte selector not matching a defined function will land
    ///      here. Decodes the standard V2 callback payload and forwards it.
    ///      Reverts if callback mismatch or if the payload is too short.
    fallback(bytes calldata _input) external returns (bytes memory) {
        require(_input.length >= 4, "input too short");
        require(_expectedCallback == msg.sender, "pool auth");
        (address sender, uint256 amount0, uint256 amount1, bytes memory data) = abi.decode(_input[4:], (address, uint256, uint256, bytes));
        uniswapV2Call(sender, amount0, amount1, data);
        return "";
    }

    /// @notice Entry point for executing an arbitrage opportunity.
    /// @dev Validates the path, determines the borrow amount if not supplied, then
    ///      initiates a flash loan or flash swap from the preferred source.
    ///      Use the `ad` return value from getProfit() as the `arb` argument here
    ///      to ensure the borrow amount and sorted pools are consistent with the simulation.
    /// @param arb           Arbitrage parameters including token path, pools, fees, and constraints.
    /// @param forceAave     If true, forces borrowing via Aave flash loan (requires AAVE_POOL set).
    /// @param forceBalancer If true, forces borrowing via Balancer flash loan (requires BALANCER_VAULT set).
    ///                      forceAave takes precedence over forceBalancer if both are true.
    ///                      If neither is true, borrows via a pool flash swap.
    function execute(ArbData memory arb, bool forceAave, bool forceBalancer) external nonReentrant onlyOwner {
        require(arb.tokens.length >= 2, "bad path");
        require(arb.pools.length == arb.tokens.length - 1, "path mismatch");
        Helper._validatePoolTokens(arb.tokens, arb.pools);

        arb = _determineBorrowAmount(arb);
        uint256 borrowAmt = arb.amountIn;

        require(borrowAmt > 0, "no arb");
        require(arb.tokens[arb.tokens.length - 1] == arb.tokenIn, 'path must end at tokenIn');
        uint256 startBalance = IERC20(arb.tokenIn).balanceOf(address(this));

        bytes memory payload = abi.encode(arb, borrowAmt, startBalance);

        if (forceAave && AAVE_POOL != address(0)) _initiateAaveFlashloan(arb, borrowAmt, payload);
        else if (forceBalancer && BALANCER_VAULT != address(0)) _initiateBalancerFlashloan(arb, borrowAmt, payload);
        else _initiatePoolFlashswap(arb, borrowAmt, payload);
    }

    /// @dev Determines the optimal borrow amount for the arb if not supplied by the caller.
    ///      Sorts pools so the borrow pool comes first, then applies the appropriate
    ///      optimal-amount formula based on whether pools are V2, V3, or mixed.
    ///      For paths with 3+ pools, the caller must supply amountIn manually.
    /// @param arb Arbitrage parameters, possibly with amountIn = 0.
    /// @return arb Updated arb with amountIn set and pools sorted.
    function _determineBorrowAmount(ArbData memory arb)
        internal
        view
        returns (ArbData memory)
    {
        require(arb.pools.length >= 2, "need at least 2 pool");

        for (uint256 i = 0; i < arb.pools.length; i++) {
            (address pt0, address pt1,) = Helper.getPoolTokens(arb.pools[i]);
            require(pt0 < pt1, "nonstandard pair");
        }

        IUniswapV2Pair p0 = IUniswapV2Pair(arb.pools[0]);
        bool borrowIs0 = (arb.tokenIn == p0.token0());
        (arb.pools, arb.tokens, arb.fees) = Helper.sortPools(arb.pools, arb.tokens, arb.fees, borrowIs0);

        if (arb.pools.length == 2) {
            IUniswapV2Pair p1 = IUniswapV2Pair(arb.pools[1]);
            require(
                p0.token0() == p1.token0() && p0.token1() == p1.token1(),
                "pools must share a common token"
            );
        }

        if (arb.amountIn > 0) return arb;

        if (arb.pools.length == 2) {
            // calcOptimalBorrow handles V2/V2, V3/V3, and V2/V3 transparently.
            // pools[] and tokens[] are already sorted by sortPools() above.
            // tokens[0] = tokenIn, tokens[1] = intermediate
            arb.amountIn = Helper.calcOptimalBorrow(arb.pools, arb.tokens, arb.fees, arb.mode);
            return arb;
        }

        require(arb.amountIn > 0, "amountIn required for 3+ pool paths");
        return arb;
    }

    /// @dev Initiates an Aave V3 flash loan for the borrow token.
    ///      Sets _expectedCallback to AAVE_POOL before the call so the
    ///      executeOperation callback can authenticate the caller.
    /// @param arb     Arbitrage parameters.
    /// @param amt     Amount to borrow.
    /// @param payload ABI-encoded (ArbData, borrowAmt, startBalance) passed through to the callback.
    function _initiateAaveFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = AAVE_POOL;

        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        uint256[] memory m = new uint256[](1); m[0] = 0;
        IAavePool(AAVE_POOL).flashLoan(address(this), a, am, m, address(this), payload, 0);

        emit FLA(arb.tokenIn, amt);
    }

    /// @dev Initiates a Balancer flash loan for the borrow token.
    ///      Sets _expectedCallback to BALANCER_VAULT before the call so the
    ///      receiveFlashLoan callback can authenticate the caller.
    /// @param arb     Arbitrage parameters.
    /// @param amt     Amount to borrow.
    /// @param payload ABI-encoded (ArbData, borrowAmt, startBalance) passed through to the callback.
    function _initiateBalancerFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = BALANCER_VAULT;

        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        IBalancerVault(BALANCER_VAULT).flashLoan(address(this), a, am, payload);

        emit FLA(arb.tokenIn, amt);
    }

    /// @dev Initiates a flash swap directly from a Uniswap V2 or V3 pool.
    ///      For V3 mode 0: uses pool.flash() on the dedicated borrowPool.
    ///      For V3 mode 1: uses pool.swap() with a negative amountSpecified to receive
    ///                     tokens upfront and repay with the other token.
    ///      For V2 mode 0: uses pair.swap() on the dedicated borrowPool.
    ///      For V2 mode 1: uses pair.swap() on pools[0], repaying with the output token.
    /// @param arb       Arbitrage parameters.
    /// @param borrowAmt Amount to borrow.
    /// @param payload   ABI-encoded callback data passed through to the pool callback.
    function _initiatePoolFlashswap(ArbData memory arb, uint256 borrowAmt, bytes memory payload) internal {
        if (Helper._isUniswapV3(arb.pools[0])) {
            if (arb.mode == 0) {
                require(arb.borrowPool != address(0), "borrowPool must be set for V3 flashloan");
                require(Helper._isContract(arb.borrowPool), "borrowPool not a contract");

                _expectedCallback = arb.borrowPool;
                (uint256 a0, uint256 a1) = arb.tokenIn == IUniswapV3Pool(arb.borrowPool).token0() ? (borrowAmt, uint256(0)) : (uint256(0), borrowAmt);
                IUniswapV3Pool(arb.borrowPool).flash(address(this), a0, a1, payload);
                emit FSV3(arb.borrowPool, borrowAmt);
            } else {
                _expectedCallback = arb.pools[0];

                (ArbData memory ad, uint256 b, uint256 c) = abi.decode(payload, (ArbData, uint256, uint256));
                bytes memory data = abi.encode(uint8(2), ad, b, c);
                bool z = (arb.tokenIn == IUniswapV3Pool(arb.pools[0]).token0());
                uint160 sqrtLimit = z ? 4295128740 : 1461446703485210103287273052203988822378723970341;
                IUniswapV3Pool(arb.pools[0]).swap(address(this), z, -int256(borrowAmt), sqrtLimit, data);
                emit FSV3(arb.pools[0], borrowAmt);
            }
            return;
        }

        if (arb.mode == 0) {
            require(arb.borrowPool != address(0), "borrowPool must be set for V2 flashloan");
            require(Helper._isContract(arb.borrowPool), "borrowPool not a contract");
        }
        IUniswapV2Pair pair = arb.mode == 0 ? IUniswapV2Pair(arb.borrowPool) : IUniswapV2Pair(arb.pools[0]);
        _expectedCallback = address(pair);

        address token0 = pair.token0();
        (uint112 r0, uint112 r1,) = pair.getReserves();

        uint256 debtAmount;
        if (arb.mode == 0) debtAmount = borrowAmt;
        else debtAmount = arb.tokenIn == token0 ? Helper.getAmountInV2(borrowAmt, r0, r1) : Helper.getAmountInV2(borrowAmt, r1, r0);

        (,,uint256 startBalance) = abi.decode(payload, (ArbData, uint256, uint256));

        V2CB memory cb = V2CB({
            arb: arb,
            borrowed: borrowAmt,
            debtToken: arb.tokenIn,
            debtAmount: debtAmount,
            startBalance: startBalance
        });

        bytes memory dat = abi.encode(cb);
        uint256 a0out; uint256 a1out;
        if (arb.mode == 0) (a0out, a1out) = (arb.tokenIn == token0) ? (borrowAmt, uint256(0)) : (uint256(0), borrowAmt);
        else (a0out, a1out) = (arb.tokenIn == token0) ? (uint256(0), borrowAmt) : (borrowAmt, uint256(0));

        pair.swap(a0out, a1out, address(this), dat);
        emit FSV2(address(pair), borrowAmt);
    }

    /// @notice Aave flash loan callback.
    /// @dev Called by the Aave pool after funds are transferred to this contract.
    ///      Executes the arb trade, then repays the loan plus Aave's premium.
    ///      Reverts if caller is not the expected Aave pool or initiator is not this contract.
    /// @param assets   Token addresses borrowed (single element array).
    /// @param amounts  Amounts borrowed (single element array).
    /// @param premiums Aave fees owed on top of the borrowed amounts.
    /// @param initiator Must equal address(this) — guards against third-party flash loan injection.
    /// @param params   ABI-encoded (ArbData, borrowAmt, startBalance).
    /// @return True on success, as required by the Aave interface.
    function executeOperation(address[] calldata assets, uint256[] calldata amounts, uint256[] calldata premiums, address initiator, bytes calldata params) external returns (bool) {
        require(msg.sender == _expectedCallback, "auth");
        _expectedCallback = address(0);

        require(initiator == address(this), "initiator");

        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(params, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        uint256 repay = amounts[0] + premiums[0];
        IERC20(assets[0]).safeTransfer(msg.sender, repay);
        _processProfit(arb, startBalance);
        return true;
    }

    /// @notice Balancer flash loan callback.
    /// @dev Called by the Balancer Vault after funds are transferred to this contract.
    ///      Executes the arb trade, then repays the loan plus any Balancer fees.
    ///      Reverts if caller is not the expected Balancer Vault.
    /// @param tokens      Token addresses borrowed.
    /// @param amounts     Amounts borrowed.
    /// @param feeAmounts  Balancer fees owed on top of the borrowed amounts.
    /// @param userData    ABI-encoded (ArbData, borrowAmt, startBalance).
    function receiveFlashLoan(address[] memory tokens, uint256[] memory amounts, uint256[] memory feeAmounts, bytes memory userData) external {
        require(msg.sender == _expectedCallback, "auth");
        _expectedCallback = address(0);

        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(userData, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        uint256 repay = amounts[0] + feeAmounts[0];
        IERC20(tokens[0]).safeTransfer(msg.sender, repay);
        _processProfit(arb, startBalance);
    }

    /// @notice Uniswap V2 flash swap callback.
    /// @dev Called by a V2 pair after tokens are transferred to this contract.
    ///      Also invoked by the fallback for non-standard V2 fork callback selectors.
    ///      Mode 0: repays the borrowed token plus 0.3% fee to the borrow pair.
    ///      Mode 1: repays the debt token (the other side of the pair) computed at initiation.
    ///      Reverts if caller is not the expected pair or sender is not this contract.
    /// @param sender  Must equal address(this) — the initiator of the flash swap.
    /// @param amount0 Amount of token0 received from the pair (0 if token1 was borrowed).
    /// @param amount1 Amount of token1 received from the pair (0 if token0 was borrowed).
    /// @param data    ABI-encoded V2CB struct containing arb params and repayment details.
    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes memory data) public {
        V2CB memory cb = abi.decode(data, (V2CB));
        require(msg.sender == _expectedCallback, "pair auth");
        _expectedCallback = address(0);

        require(sender == address(this), "sender");

        uint256 borrowed = amount0 > 0 ? amount0 : amount1;
        address borrowToken = cb.arb.tokenIn;
        address debtToken = cb.debtToken;
        uint256 debtAmt = cb.debtAmount;

        uint256 startIdx = cb.arb.mode == 0 ? 0 : 1;
        uint256 startTokenIdx = startIdx;
        _executeTrade(cb.arb, borrowed, startIdx, startTokenIdx);

        if (cb.arb.mode == 0) {
            // Mode 0: repay same token borrowed plus 0.3% fee
            uint256 fee = (borrowed * 3) / 1000;
            uint256 repay = borrowed + fee;
            require(IERC20(borrowToken).balanceOf(address(this)) >= repay, "insuf");
            IERC20(borrowToken).safeTransfer(msg.sender, repay);
        } else {
            // Mode 1: repay with the other token, amount pre-computed at initiation
            require(IERC20(debtToken).balanceOf(address(this)) >= debtAmt, "insuf debt");
            IERC20(debtToken).safeTransfer(msg.sender, debtAmt);
        }

        _processProfit(cb.arb, cb.startBalance);
    }

    /// @notice Uniswap V3 swap callback.
    /// @dev Called by a V3 pool during swap execution.
    ///      Handles two internal modes encoded in the data payload:
    ///      Mode 1 (internal swap hop): called during _swap() for each V3 hop in the trade path.
    ///                                  Transfers the owed token directly to the pool and returns.
    ///      Mode 2 (flash swap entry):  called when pools[0] is used as the flash swap source.
    ///                                  Executes the arb trade starting from pools[1], then repays
    ///                                  the owed amounts to pools[0].
    ///      Reverts if caller is not the expected pool.
    /// @param a0   Amount of token0 owed to the pool (positive) or received (negative).
    /// @param a1   Amount of token1 owed to the pool (positive) or received (negative).
    /// @param data ABI-encoded payload beginning with a uint8 mode discriminator.
    function uniswapV3SwapCallback(int256 a0, int256 a1, bytes calldata data) external {
        require(msg.sender == _expectedCallback, "pool auth");

        uint8 mode = abi.decode(data, (uint8));
        if (mode == 1) {
            // Internal hop repayment: transfer the owed token to the pool
            (, address tokenIn, ) = abi.decode(data, (uint8, address, address));
            address req = a0 > 0 ? IUniswapV3Pool(msg.sender).token0() : IUniswapV3Pool(msg.sender).token1();
            uint256 need = a0 > 0 ? uint256(a0) : uint256(a1);
            require(req == tokenIn, "mismatch");
            require(IERC20(req).balanceOf(address(this)) >= need, "bal low");
            IERC20(req).safeTransfer(msg.sender, need);
            return;
        }

        // Mode 2: flash swap entry — execute trade then repay pools[0]
        _expectedCallback = address(0);

        (, ArbData memory arb,, uint256 startBalance) = abi.decode(data, (uint8, ArbData, uint256, uint256));

        bool borrowedIs0 = a0 < 0;
        uint256 borrowed = borrowedIs0 ? uint256(-a0) : uint256(-a1);
        address t0 = IUniswapV3Pool(msg.sender).token0();
        address t1 = IUniswapV3Pool(msg.sender).token1();
        address debtToken = borrowedIs0 ? t1 : t0;

        address finalToken = arb.tokens[arb.tokens.length - 1];
        require(debtToken == finalToken, "Mode 1: Path must end with Debt Token");

        // Execute trade starting from pool index 1, skipping the flash swap pool
        uint256 startIdx = 1;
        uint256 startTokenIdx = startIdx;
        _executeTrade(arb, borrowed, startIdx, startTokenIdx);

        // Repay the V3 pool whatever it is owed
        if (a0 > 0) {
            uint256 owe0 = uint256(a0);
            require(IERC20(t0).balanceOf(address(this)) >= owe0, "insuf0");
            IERC20(t0).safeTransfer(msg.sender, owe0);
        }
        if (a1 > 0) {
            uint256 owe1 = uint256(a1);
            require(IERC20(t1).balanceOf(address(this)) >= owe1, "insuf1");
            IERC20(t1).safeTransfer(msg.sender, owe1);
        }

        _processProfit(arb, startBalance);
    }

    /// @notice Uniswap V3 flash callback.
    /// @dev Called by a V3 pool after pool.flash() transfers tokens to this contract.
    ///      Executes the arb trade then repays the pool the borrowed amount plus fees.
    ///      Reverts if caller is not the expected pool.
    /// @param f0   Fee owed on token0 (0 if token1 was borrowed).
    /// @param f1   Fee owed on token1 (0 if token0 was borrowed).
    /// @param data ABI-encoded (ArbData, borrowAmt, startBalance).
    function uniswapV3FlashCallback(uint256 f0, uint256 f1, bytes calldata data) external {
        require(msg.sender == _expectedCallback, "pool auth");
        _expectedCallback = address(0);

        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(data, (ArbData, uint256, uint256));

        _executeTrade(arb, borrowed, 0, 0);
        IUniswapV3Pool pool = IUniswapV3Pool(arb.pools[0]);
        address t0 = pool.token0();
        address t1 = pool.token1();
        if (f0 > 0) { uint256 owe0 = borrowed + f0; require(IERC20(t0).balanceOf(address(this)) >= owe0, "insuf"); IERC20(t0).safeTransfer(msg.sender, owe0); }
        if (f1 > 0) { uint256 owe1 = borrowed + f1; require(IERC20(t1).balanceOf(address(this)) >= owe1, "insuf"); IERC20(t1).safeTransfer(msg.sender, owe1); }
        _processProfit(arb, startBalance);
    }

    /// @dev Executes the arb trade by swapping through each pool in the path sequentially.
    ///      Each hop's output becomes the next hop's input.
    /// @param arb           Arbitrage parameters containing the pool and token path.
    /// @param borrowed      The initial amount to swap into the first pool.
    /// @param startPoolIdx  Index into arb.pools to begin execution from.
    ///                      Non-zero in mode 1 to skip the flash swap pool.
    /// @param startTokenIdx Index into arb.tokens corresponding to startPoolIdx.
    function _executeTrade(ArbData memory arb, uint256 borrowed, uint256 startPoolIdx, uint256 startTokenIdx) internal {
        address curToken = arb.tokens[startTokenIdx];
        uint256 amt = borrowed;
        uint256 hopIdx = startTokenIdx;
        for (uint i = startPoolIdx; i < arb.pools.length; i++) {
            address pool = arb.pools[i];
            address nextToken = arb.tokens[hopIdx + 1];
            amt = _swap(pool, curToken, nextToken, amt);
            curToken = nextToken;
            hopIdx++;
        }
    }

    /// @dev Executes a single token swap on either a V2 pair or V3 pool.
    ///      For V3: uses pool.swap() with an exact-input amount. Sets and clears
    ///              _expectedCallback around the call so uniswapV3SwapCallback can authenticate.
    ///      For V2: computes amountOut from reserves before transferring, then calls pair.swap().
    /// @param pool     Address of the V2 pair or V3 pool to swap on.
    /// @param tokenIn  Token being sold.
    /// @param tokenOut Token being bought.
    /// @param amountIn Exact amount of tokenIn to swap.
    /// @return out     Amount of tokenOut received.
    function _swap(address pool, address tokenIn, address tokenOut, uint256 amountIn) internal returns (uint256 out) {
        if (Helper._isUniswapV3(pool)) {
            IUniswapV3Pool p = IUniswapV3Pool(pool);
            bool z = (tokenIn == p.token0());
            uint160 sqrtLimit = z ? 4295128740 : 1461446703485210103287273052203988822378723970341;

            _expectedCallback = pool;
            (int256 a0, int256 a1) = p.swap(address(this), z, int256(amountIn), sqrtLimit, abi.encode(uint8(1), tokenIn, tokenOut));
            _expectedCallback = address(0);

            out = z ? uint256(-int256(a1)) : uint256(-int256(a0));
            return out;
        }

        // V2: compute output from reserves before transferring to avoid reserve manipulation
        IUniswapV2Pair p2 = IUniswapV2Pair(pool);
        (uint112 r0, uint112 r1,) = p2.getReserves();
        (uint256 rin, uint256 rout) = tokenIn == p2.token0() ? (uint256(r0), uint256(r1)) : (uint256(r1), uint256(r0));
        out = Helper.getAmountOutV2(amountIn, rin, rout);
        IERC20(tokenIn).safeTransfer(pool, amountIn);
        uint256 o0 = tokenOut == p2.token0() ? out : 0;
        uint256 o1 = tokenOut == p2.token0() ? 0 : out;
        p2.swap(o0, o1, address(this), "");
    }

    /// @dev Computes the profit after the arb completes and transfers it to the owner.
    ///      Profit is defined as the increase in tokenIn balance relative to startBalance,
    ///      measured after all repayments have been made by the caller.
    ///      For WETH profits, unwraps to ETH before transferring.
    ///      Reverts if no profit was made or if profit is below arb.minProfit.
    /// @param arb          Arbitrage parameters, used for tokenIn and minProfit.
    /// @param startBalance tokenIn balance recorded before the flash loan was initiated.
    function _processProfit(ArbData memory arb, uint256 startBalance) internal {
        if (arb.tokenIn == address(0)) return;

        uint256 endBalance = IERC20(arb.tokenIn).balanceOf(address(this));
        require(endBalance > startBalance, "no profit after repay");

        uint256 profit = endBalance - startBalance;
        require(profit >= arb.minProfit, "min profit not met");

        emit DONE(arb.tokenIn, profit);

        if (arb.tokenIn == WETH) {
            IWETH(WETH).withdraw(profit);
            (bool ok,) = payable(owner()).call{value: profit}("");
            require(ok, "ETH transfer failed");
        } else {
            IERC20(arb.tokenIn).safeTransfer(owner(), profit);
        }
    }

    /// @notice Simulates an arb opportunity and returns the expected profit.
    /// @dev Safe to call from view contexts and other contracts since it uses the view-only Quoter.
    ///      Internally calls _determineBorrowAmount to sort pools and set amountIn if not supplied.
    ///      V3 hops are simulated via the Quoter; V2 hops use the constant-product reserve formula.
    ///      The returned `ad` struct should be passed directly to execute() to ensure the borrow
    ///      amount and pool ordering used in simulation match what execute() will use.
    /// @param arb Arbitrage parameters to simulate. amountIn may be 0 for auto-calculation.
    /// @return ad     Updated ArbData with amountIn set and pools sorted — pass this to execute().
    /// @return profit Expected profit in tokenIn after repaying the borrow. 0 means not profitable.
    function getProfit(ArbData memory arb)
        public
        view
        returns (
            ArbData memory ad, // ← use this in execute(), not your original arb, to ensure consistency between simulation and execution
            uint256 profit // The expected profit delta after repaying the borrow, which may differ from final balance - initial balance if mode 1
        )
    {
        ad = _determineBorrowAmount(arb);
        require(ad.amountIn > 0, "no arb");

        require(ad.pools.length == ad.tokens.length - 1, "invalid pools/tokens length");
        require(ad.pools.length == ad.fees.length, "pools/fees mismatch");

        uint256 current = ad.amountIn;
        uint256 startIdx = ad.mode == 1 ? 1 : 0;

        for (uint256 i = startIdx; i < ad.pools.length; i++) {
            address pool     = ad.pools[i];
            address tokenIn  = ad.tokens[i];
            address tokenOut = ad.tokens[i + 1];

            if (Helper._isUniswapV3(pool)) {
                uint24 fee = ad.fees.length > i ? ad.fees[i] : 3000;
                (current,,,) = IQuoter(Quoter).quoteExactInputSingle(
                    IQuoter.QuoteExactInputSingleParams({
                        tokenIn:            tokenIn,
                        tokenOut:           tokenOut,
                        amountIn:           current,
                        fee:                fee,
                        sqrtPriceLimitX96:  0
                    })
                ); 
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool).getReserves();
                address t0 = IUniswapV2Pair(pool).token0();
                current = tokenIn == t0
                    ? Helper.getAmountOutV2(current, r0, r1)
                    : Helper.getAmountOutV2(current, r1, r0);
            }
        }

        uint256 outAmount = current;

        if (ad.mode == 0) {
            profit = outAmount > ad.amountIn ? outAmount - ad.amountIn : 0;
        } else {
            // Mode 1: debt is what pool[0] requires to give us `borrow` of tokenIn
            uint256 debtAmount;
            address pool0 = ad.pools[0];

            if (Helper._isUniswapV3(pool0)) {
                uint24 fee0 = ad.fees[0];
                (debtAmount,,,) = IQuoter(Quoter).quoteExactOutputSingle(
                    IQuoter.QuoteExactOutputSingleParams({
                        tokenIn:           ad.tokens[0],
                        tokenOut:          ad.tokens[1],
                        amount:          ad.amountIn,
                        fee:               fee0,
                        sqrtPriceLimitX96: 0
                    })
                );
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool0).getReserves();
                address t0 = IUniswapV2Pair(pool0).token0();
                debtAmount = ad.tokens[0] == t0
                    ? Helper.getAmountInV2(ad.amountIn, r0, r1)
                    : Helper.getAmountInV2(ad.amountIn, r1, r0);
            }

            profit = outAmount > debtAmount ? outAmount - debtAmount : 0;
        }

        return (ad, profit);
    }

    /// @notice Withdraws tokens or ETH from the contract to the owner.
    /// @dev Passing amount = 0 withdraws the entire balance of the token.
    ///      Passing token = address(0) ignores amount and withdraws all ETH.
    /// @param token The ERC20 token address to withdraw, or address(0) for ETH.
    /// @param amount The amount to withdraw, or 0 to withdraw the full balance.
    function withdraw(address token, uint256 amount) external onlyOwner {
        if (token == address(0)) {
            // ETH path: amount is ignored, always withdraws full contract balance
            (bool ok,) = payable(owner()).call{value: address(this).balance}("");
            require(ok, "ETH withdraw failed");
        } else {
            uint256 bal = IERC20(token).balanceOf(address(this));
            if (amount != 0) {
                // Partial withdrawal: caller must not request more than available
                require(bal >= amount, "insuf bal");
                IERC20(token).safeTransfer(owner(), amount);
            } else {
                // Full withdrawal: transfer entire token balance
                IERC20(token).safeTransfer(owner(), bal);
            }
        }
    }
}