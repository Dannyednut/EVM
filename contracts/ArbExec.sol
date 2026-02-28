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

    constructor(address _w, address _q, address _a, address _b) Ownable(msg.sender) {
        require(_w != address(0), "zero WETH");
        require(_q != address(0), "zero Quoter");
        WETH = _w;
        Quoter = _q;
        AAVE_POOL = _a;
        BALANCER_VAULT = _b;
    }

    receive() external payable {}
    
    /// @dev Redirect uniswap callback function
    /// The callback function on different DEX are not same, so use a fallback to redirect to uniswapV2Call
    fallback(bytes calldata _input) external returns (bytes memory) {
        require(_input.length >= 4, "input too short");
        require(_expectedCallback != address(0), "no pending callback");
        (address sender, uint256 amount0, uint256 amount1, bytes memory data) = abi.decode(_input[4:], (address, uint256, uint256, bytes));
        uniswapV2Call(sender, amount0, amount1, data);

        return "";
    }

    // -------- execute entry --------
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

    // -------- borrow amount & prep -------
    // ─────────────────────────────────────────────
    // Borrow amount calculation
    // ─────────────────────────────────────────────
    function _determineBorrowAmount(ArbData memory arb)
        internal
        view
        returns (ArbData memory)
    {
        require(arb.pools.length >= 2, "need at least 2 pool");

        // Validate ordering for all pools
        for (uint256 i = 0; i < arb.pools.length; i++) {
            (address pt0, address pt1,) = Helper.getPoolTokens(arb.pools[i]);
            require(pt0 < pt1, "nonstandard pair");
        }

        IUniswapV2Pair p0 = IUniswapV2Pair(arb.pools[0]);
        bool borrowIs0 = (arb.tokenIn == p0.token0());
        (arb.pools, arb.tokens) = Helper.sortPools(arb.pools, arb.tokens, borrowIs0);

        if (arb.pools.length == 2) {
            IUniswapV2Pair p1 = IUniswapV2Pair(arb.pools[1]);
            require(
                p0.token0() == p1.token0() && p0.token1() == p1.token1(),
                "pools must share a common token"
            );
        }

        // Use caller-supplied amount if provided
        if (arb.amountIn > 0) return arb;

        if (arb.pools.length == 2) {
            bool v3_0 = Helper._isUniswapV3(arb.pools[0]);
            bool v3_1 = Helper._isUniswapV3(arb.pools[1]);
            uint256 borrowAmt;

            if (!v3_0 && !v3_1) {
                // Pure V2 two-pool case
                (uint112 r0,  uint112 r1,)  = IUniswapV2Pair(arb.pools[0]).getReserves();
                (uint112 rs0, uint112 rs1,) = IUniswapV2Pair(arb.pools[1]).getReserves();

                uint256 resInLow   = borrowIs0 ? uint256(r0)  : uint256(r1);
                uint256 resOutLow  = borrowIs0 ? uint256(r1)  : uint256(r0);
                uint256 resInHigh  = borrowIs0 ? uint256(rs1) : uint256(rs0);
                uint256 resOutHigh = borrowIs0 ? uint256(rs0) : uint256(rs1);

                borrowAmt = Helper.calcOptimalV2Borrow(
                    resInLow, resOutLow, resInHigh, resOutHigh, arb.mode
                );
                arb.amountIn = borrowAmt;
                return arb;
            }else if (v3_0 && v3_1) {
                // Pure V3 two-pool case
                borrowAmt = Helper.estimateOptimalV3Borrow(arb.pools, arb.fees, Quoter);
                arb.amountIn = borrowAmt;
                return arb;
            }
            // Mixed or multi-hop
            borrowAmt = Helper.calcOptimalV2V3(arb.pools, arb.mode);
            arb.amountIn = borrowAmt;
            return arb;
            
        }

        // 3+ pools: auto-calculation not supported, caller must supply amountIn
        require(arb.amountIn > 0, "amountIn required for 3+ pool paths");
        return arb;
    }

    // -------- initiators --------
    function _initiateAaveFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = AAVE_POOL;

        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        uint256[] memory m = new uint256[](1); m[0] = 0;
        IAavePool(AAVE_POOL).flashLoan(address(this), a, am, m, address(this), payload, 0);

        emit FLA(arb.tokenIn, amt);
    }

    function _initiateBalancerFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = BALANCER_VAULT;

        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        IBalancerVault(BALANCER_VAULT).flashLoan(address(this), a, am, payload);

        emit FLA(arb.tokenIn, amt);
    }

    function _initiatePoolFlashswap(ArbData memory arb, uint256 borrowAmt, bytes memory payload) internal {
        if (Helper._isUniswapV3(arb.pools[0])) {
            if (arb.mode == 0) {
                // V3 flash loan from a dedicated borrow pool
                require(arb.borrowPool != address(0), "borrowPool must be set for V3 flashloan");
                require(Helper._isContract(arb.borrowPool), "borrowPool not a contract");

                _expectedCallback = arb.borrowPool;
                (uint256 a0, uint256 a1) = arb.tokenIn == IUniswapV3Pool(arb.borrowPool).token0() ? (borrowAmt, uint256(0)) : (uint256(0), borrowAmt);
                IUniswapV3Pool(arb.borrowPool).flash(address(this), a0, a1, payload);
                emit FSV3(arb.borrowPool, borrowAmt);
            } else {
                // Mode 1: V3 flash swap — borrow by swapping, repay with the other token
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

        // V2 path
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

    // -------- AAVE callback --------
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

    // -------- Balancer callback --------
    function receiveFlashLoan(address[] memory tokens, uint256[] memory amounts, uint256[] memory feeAmounts, bytes memory userData) external {
        require(msg.sender == _expectedCallback, "auth");
        _expectedCallback = address(0);

        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(userData, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        uint256 repay = amounts[0] + feeAmounts[0];
        IERC20(tokens[0]).safeTransfer(msg.sender, repay);
        _processProfit(arb, startBalance);
    }

    // -------- V2 flashswap callback --------
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

        // repay borrow pair
        if (cb.arb.mode == 0) {
            uint256 fee = (borrowed * 3) / 1000;
            uint256 repay = borrowed + fee;
            require(IERC20(borrowToken).balanceOf(address(this)) >= repay, "insuf");
            IERC20(borrowToken).safeTransfer(msg.sender, repay);
        } else {
            require(IERC20(debtToken).balanceOf(address(this)) >= debtAmt, "insuf debt");
            IERC20(debtToken).safeTransfer(msg.sender, debtAmt);
        }

        _processProfit(cb.arb, cb.startBalance);
    }

    // -------- V3 swap callback -------
    function uniswapV3SwapCallback(int256 a0, int256 a1, bytes calldata data) external {
        require(msg.sender == _expectedCallback, "pool auth");

        uint8 mode = abi.decode(data, (uint8));
        if (mode == 1) {
            (, address tokenIn, ) = abi.decode(data, (uint8, address, address));
            address req = a0 > 0 ? IUniswapV3Pool(msg.sender).token0() : IUniswapV3Pool(msg.sender).token1();
            uint256 need = a0 > 0 ? uint256(a0) : uint256(a1);
            require(req == tokenIn, "mismatch");
            require(IERC20(req).balanceOf(address(this)) >= need, "bal low");
            IERC20(req).safeTransfer(msg.sender, need);
            return;
        }

        _expectedCallback = address(0);

        (, ArbData memory arb,, uint256 startBalance ) = abi.decode(data, (uint8, ArbData, uint256, uint256));

        bool borrowedIs0 = a0 < 0;
        uint256 borrowed = borrowedIs0 ? uint256(-a0) : uint256(-a1);
        address t0 = IUniswapV3Pool(msg.sender).token0();
        address t1 = IUniswapV3Pool(msg.sender).token1();
        address debtToken = borrowedIs0 ? t0 : t1;

        // repay-with-other: sell borrowedToken on poolOut
        address finalToken = arb.tokens[arb.tokens.length - 1];
        require(debtToken == finalToken, "Mode 1: Path must end with Debt Token");
        
        // Execute starting from pool index 1
        uint256 startIdx = 1;
        uint256 startTokenIdx = startIdx;
        _executeTrade(arb, borrowed, startIdx, startTokenIdx);

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


    // -------- V3 flash callback -------
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

    // -------- Core execution --------
    function _executeTrade(ArbData memory arb, uint256 borrowed, uint256 startPoolIdx, uint256 startTokenIdx) internal  {
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
        // V2: Fetch reserves BEFORE transfer to compute accurate amountOut
        IUniswapV2Pair p2 = IUniswapV2Pair(pool);
        (uint112 r0, uint112 r1,) = p2.getReserves();
        (uint256 rin, uint256 rout) = tokenIn == p2.token0() ? (uint256(r0), uint256(r1)) : (uint256(r1), uint256(r0));
        out = Helper.getAmountOutV2(amountIn, rin, rout);
        // Transfer after computation
        IERC20(tokenIn).safeTransfer(pool, amountIn);
        uint256 o0 = tokenOut == p2.token0() ? out : 0;
        uint256 o1 = tokenOut == p2.token0() ? 0 : out;
        p2.swap(o0, o1, address(this), "");
    }

    // -------- Profit handling (emit before transfer) --------
    function _processProfit(ArbData memory arb, uint256 startBalance) internal {
        if (arb.tokenIn == address(0)) return;

        uint256 endBalance = IERC20(arb.tokenIn).balanceOf(address(this));
        require(endBalance > startBalance, "no profit after repay");

        uint256 profit = endBalance - startBalance;
        require(profit >= arb.minProfit, "min profit not met");

        // Fix #4: emit the true profit delta, not total balance
        emit DONE(arb.tokenIn, profit);

        if (arb.tokenIn == WETH) {
            IWETH(WETH).withdraw(profit);
            // Fix #15: use .call instead of .transfer
            (bool ok,) = payable(owner()).call{value: profit}("");
            require(ok, "ETH transfer failed");
        } else {
            // Fix #11: transfer only the profit, not any pre-existing balance
            IERC20(arb.tokenIn).safeTransfer(owner(), profit);
        }
    }

    // ─────────────────────────────────────────────
    // Profitability simulation (view)
    // ─────────────────────────────────────────────
    function getProfit(ArbData memory arb)
        public
        view
        returns (
            ArbData memory ad, // ← use this in execute(), not your original arb, to ensure consistency between simulation and execution
            uint256 profit // The expected profit delta after repaying the borrow, which may differ from final balance - initial balance if mode 1
        )
    {
        ad = _determineBorrowAmount(arb);
        require(ad.amountIn > 0, "bad amt");

        require(ad.pools.length == ad.tokens.length - 1, "invalid pools/tokens length");

        uint256 current = ad.amountIn;
        uint256 startIdx = ad.mode == 1 ? 1 : 0;

        for (uint256 i = startIdx; i < ad.pools.length; i++) {
            address pool     = ad.pools[i];
            address tokenIn  = ad.tokens[i];
            address tokenOut = ad.tokens[i + 1];

            if (Helper._isUniswapV3(pool)) {
                uint24 fee = ad.fees.length > i ? ad.fees[i] : 3000;
                try IQuoter(Quoter).quoteExactInputSingle(
                    IQuoter.QuoteExactInputSingleParams({
                        tokenIn:            tokenIn,
                        tokenOut:           tokenOut,
                        amountIn:           current,
                        fee:                fee,
                        sqrtPriceLimitX96:  0
                    })
                ) returns (uint256 amountOut, uint160, uint32, uint256) {
                    current = amountOut;
                } catch {
                    return (ad, 0);
                }
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
                uint24 fee0 = ad.fees.length > 0 ? ad.fees[0] : 3000;
                try IQuoter(Quoter).quoteExactInputSingle(
                    IQuoter.QuoteExactInputSingleParams({
                        tokenIn:           ad.tokens[0],
                        tokenOut:          ad.tokens[1],
                        amountIn:          ad.amountIn,
                        fee:               fee0,
                        sqrtPriceLimitX96: 0
                    })
                ) returns (uint256 amountOut, uint160, uint32, uint256) {
                    debtAmount = amountOut;
                } catch {
                    return (ad, 0);
                }
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


    // emergency
    function withdraw(address token, uint256 amount) external onlyOwner {
        if (token == address(0)) {
            (bool ok,) = payable(owner()).call{value: address(this).balance}("");
            require(ok, "ETH withdraw failed");
        } else {
            uint256 bal = IERC20(token).balanceOf(address(this));
            if (amount != 0) {
                require(bal >= amount, "insuf bal");
                IERC20(token).safeTransfer(owner(), amount);
            }else IERC20(token).safeTransfer(owner(), bal);
        }
    }

}