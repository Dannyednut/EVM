// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

import "./interfaces/IUniswapV2Pair.sol";
import "./interfaces/IUniswapV3Pool.sol";
import "./interfaces/IQuoter.sol";
import "./interfaces/IWETH.sol";
import "./interfaces/IBalancerVault.sol";
import {Helper} from "./libraries/HelperV3.sol";

struct Data {
    uint256 amountIn;
    uint256 minProfit;
    address[] tokens;
    address[] pools;
    uint24[] fees;
    address tokenIn;
    uint8 mode; // 0 = borrow token in, 1 = borrow other token
}


// Custom errors — 4 bytes vs N bytes for require strings
error Auth();
error Block();
error BadPath();
error NoProfit();
error ZeroAddress();
error AmountRequired();
error TransferFailed();
error ModePathMismatch();
error InsufficientBalance();

contract Exec is Ownable, ReentrancyGuard {

    address private immutable WETH;
    address private immutable Quoter;
    address private immutable BALANCER_VAULT;

    // Set before initiating any flash loan/swap, validated inside every callback,
    // and cleared immediately after validation to prevent re-use.
    address private _expectedCallback;

    event DONE(address indexed token, uint256 amt);
    event BATCH(uint256 successful, uint256 failed);

    /// @notice Deploys the contract and sets immutable protocol addresses.
    /// @param _w  WETH token address used for unwrapping profits.
    /// @param _q  View-only Quoter address for simulating V3 swap outputs.
    /// @param _b  Balancer Vault address, or address(0) to disable Balancer flash loans.
    constructor(address _w, address _q, address _b) Ownable(msg.sender) {
        if (_w == address(0) || _q == address(0)) revert ZeroAddress();
        WETH = _w;
        Quoter = _q;
        BALANCER_VAULT = _b;
    }

    /// @dev Accepts ETH from WETH.withdraw() during profit unwrapping.
    receive() external payable {}

    /// @dev Redirects non-standard V2 fork swap callbacks (e.g. pancakeV2Call, sushiCall)
    ///      to uniswapV2Call. Any 4-byte selector not matching a defined function will land
    ///      here. Decodes the standard V2 callback payload and forwards it.
    ///      Reverts if callback mismatch or if the payload is too short.
    fallback(bytes calldata _input) external returns (bytes memory) {
        if (_input.length < 4) revert BadPath();
        if (_expectedCallback != msg.sender) revert Auth();
        (address sender, uint256 amount0, uint256 amount1, bytes memory data) = abi.decode(_input[4:], (address, uint256, uint256, bytes));
        uniswapV2Call(sender, amount0, amount1, data);
        return "";
    }

    /**
     * @notice Executes multiple arbs. Continues on failure.
     *         Forwards all DONE events from successful executions.
     */
    function multiCall(bytes[] calldata calls) external onlyOwner returns (uint256 successful, uint256 failed) {
        uint256 len = calls.length;
        successful = 0;

        for (uint256 i = 0; i < len; ) {
            // Strip first 32 bytes (junk_hash), execute remaining calldata
            // bytes memory realData = new bytes(calls[i].length - 32);
            // for(uint j=32; j<calls[i].length; j++) {
            //     realData[j-32] = calls[i][j];
            // }
            // (bool success,) = address(this).call(calls[i]);   // call swap()

            // if (success) {
            //     successful++;
            // }

            bytes calldata input = calls[i];
            if (input.length <= 32) {  // Skip invalid
                unchecked { ++i; continue; }
            }
            
            // Assembly byte copy (gas efficient)
            bytes memory realData;
            assembly {
                let inLen := mload(input)
                let realLen := sub(inLen, 32)
                
                // Allocate realData
                realData := mload(0x40)
                mstore(0x40, add(realData, add(0x20, realLen)))
                mstore(realData, realLen)
                
                // Copy bytes[32:end] → realData[0:end-32]
                calldatacopy(add(realData, 0x20), add(input.offset, 0x20), realLen)
            }
            
            // CALL with ALL remaining gas (important for nested swaps)
            (bool success, ) = address(this).call{gas: gas()}(realData);
            
            // Allow failure → continue (don't revert bundle)
            if (success) {
                successful++;
            }
            
            unchecked { ++i; }
        }

        failed = len - successful;
        emit BATCH(successful, failed);
    }

    /// @notice Entry point for executing an arbitrage opportunity.
    /// @dev Validates the path, determines the borrow amount if not supplied, then
    ///      initiates a flash loan or flash swap from the preferred source.
    ///      Use the `ad` return value from yieldOut() as the `arb` argument here
    ///      to ensure the borrow amount and sorted pools are consistent with the simulation.
    /// @param arb           Arbitrage parameters including token path, pools, fees, and constraints.
    /// @param lender If true, forces borrowing via Balancer flash loan (requires BALANCER_VAULT set).
    ///                      If not true, borrows via a pool flash swap.
    function swap(Data calldata arb, bool lender, uint256 builderFeeBps, uint256 validUntilBlock) external nonReentrant {
        // Allow calls from owner directly OR from this contract (via multiCall)
        if (msg.sender != owner() && msg.sender != address(this)) revert Auth();
        if (block.number > validUntilBlock) revert Block();
        if (arb.tokens.length < 2) revert BadPath();
        if (arb.pools.length != arb.tokens.length - 1) revert BadPath();
        Helper._validatePoolTokens(arb.tokens, arb.pools);

        // Copy calldata to memory so _determineBorrow can mutate (sort pools, set amountIn)
        Data memory arbMem = arb; uint256 profit;
        (arbMem, profit) = yieldOut(arbMem);
        uint256 borrowAmt = arbMem.amountIn;

        if (profit < arbMem.minProfit || profit == 0) revert NoProfit();
        if (borrowAmt == 0) revert AmountRequired();
        if (arbMem.tokens[arbMem.tokens.length - 1] != arbMem.tokenIn) revert BadPath();
        uint256 startBalance = Helper._balanceOf(arbMem.tokenIn, address(this));

        bytes memory payload = abi.encode(arbMem, borrowAmt);

        if (lender && BALANCER_VAULT != address(0)) _initiateFlashloan(arbMem, borrowAmt, payload);
        else _initiateFlashswap(arbMem, borrowAmt, payload);
        _processProfit(arbMem, startBalance, builderFeeBps);
    }

    /// @dev Determines the optimal borrow amount for the arb if not supplied by the caller.
    ///      Sorts pools so the borrow pool comes first, then applies the appropriate
    ///      optimal-amount formula based on whether pools are V2, V3, or mixed.
    ///      For paths with 3+ pools, the caller must supply amountIn manually.
    /// @param arb Arbitrage parameters, possibly with amountIn = 0.
    /// @return arb Updated arb with amountIn set and pools sorted.
    function _determineBorrow(Data memory arb)
        internal
        view
        returns (Data memory)
    {
        if (arb.pools.length < 2) revert BadPath();

        if (arb.pools.length == 2) {
            bool borrowIs0 = (arb.tokenIn == Helper._token0(arb.pools[0]));
            (arb.pools, arb.tokens, arb.fees) = Helper.sortPools(arb.pools, arb.tokens, arb.fees, borrowIs0);
        
            require(
                Helper._token0(arb.pools[0]) == Helper._token0(arb.pools[1]) &&
                Helper._token1(arb.pools[0]) == Helper._token1(arb.pools[1]),
                "pools must share a common token"
            );
        }

        if (arb.amountIn > 0) return arb;
        arb.amountIn = Helper.calcOptimalBorrow(Quoter, arb.pools, arb.tokens, arb.fees, arb.mode);
        return arb;
    }

    /// @dev Initiates a Balancer flash loan for the borrow token.
    ///      Sets _expectedCallback to BALANCER_VAULT before the call so the
    ///      receiveFlashLoan callback can authenticate the caller.
    /// @param arb     Arbitrage parameters.
    /// @param amt     Amount to borrow.
    /// @param payload ABI-encoded (Data, borrowAmt) passed through to the callback.
    function _initiateFlashloan(Data memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = BALANCER_VAULT;

        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        try IBalancerVault(BALANCER_VAULT).flashLoan(address(this), a, am, payload) {
        } catch {
            _expectedCallback = address(0);
            // revert("Balancer FL failed");
            (uint256 resIn, uint256 resOut) = Helper._getOrderedReserves(arb.pools[0], arb.tokenIn);
            (arb.amountIn, arb.mode) = (Helper.getAmountOutV2WithFee(arb.amountIn, resIn, resOut, arb.fees[0]), 1);

            _initiateFlashswap(arb, arb.amountIn, abi.encode(arb, arb.amountIn));
        }
    }

    /// @dev Initiates a flash swap directly from a Uniswap V2 or V3 pool.
    ///      For V3 mode 1: uses pool.swap() with a negative amountSpecified to receive
    ///                     tokens upfront and repay with the other token.
    ///      For V2 mode 1: uses pair.swap() on pools[0], repaying with the output token.
    /// @param arb       Arbitrage parameters.
    /// @param borrowAmt Amount to borrow.
    /// @param payload   ABI-encoded callback data passed through to the pool callback.
    function _initiateFlashswap(Data memory arb, uint256 borrowAmt, bytes memory payload) internal {
        if (Helper._isUniswapV3(arb.pools[0])) {
            if (arb.mode == 0) revert BadPath();
            _expectedCallback = arb.pools[0];
            bool z = (arb.tokenIn == Helper._token0(arb.pools[0]));
            uint160 sqrtLimit = z ? 4295128740 : 1461446703485210103287273052203988822378723970341;
            // Prepend mode discriminator (2) to payload for callback dispatch
            // bytes memory data = abi.encodePacked(uint8(2), payload);
            (Data memory ad, uint256 b) = abi.decode(payload, (Data, uint256));
            bytes memory data = abi.encode(uint8(2), ad, b);
            IUniswapV3Pool(arb.pools[0]).swap(address(this), z, -int256(borrowAmt), sqrtLimit, data);
            
            return;
        }

        IUniswapV2Pair pair = IUniswapV2Pair(arb.pools[0]);
        _expectedCallback = address(pair);

        address token0 = Helper._token0(address(pair));
        bool isT0 = arb.tokenIn == token0;

        uint256 a0out; uint256 a1out;
        (a0out, a1out) = isT0 ? (uint256(0), borrowAmt) : (borrowAmt, uint256(0));

        // Pass payload directly — uniswapV2Call recomputes debtAmount on-the-fly
        try pair.swap(a0out, a1out, address(this), payload) {
            // _expectedCallback cleared inside uniswapV2Call callback
        } catch {
            _expectedCallback = address(0);
            revert("V2 swap flash failed");
        }
    }

    function receiveFlashLoan(address[] memory tokens, uint256[] memory amounts, uint256[] memory feeAmounts, bytes memory userData) external {
        if (msg.sender != _expectedCallback) revert Auth();
        _expectedCallback = address(0);
        (Data memory arb, uint256 borrowed) = abi.decode(userData, (Data, uint256));
        _execute(arb, borrowed, 0, 0);
        Helper._safeTransfer(tokens[0], msg.sender, amounts[0] + feeAmounts[0]);
    }

    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes memory data) public {
        if (msg.sender != _expectedCallback) revert Auth();
        _expectedCallback = address(0);
        if (sender != address(this)) revert Auth();

        (Data memory arb, uint256 borrowed) = abi.decode(data, (Data, uint256));
        // amount0/amount1 tells us what was actually received — use it directly
        borrowed = amount0 > 0 ? amount0 : amount1;

        _execute(arb, borrowed, 1, 1);
        
        // Mode 1: recompute debtAmount from current reserves
        address token0 = Helper._token0(msg.sender);
        (uint112 r0, uint112 r1,) = IUniswapV2Pair(msg.sender).getReserves();
        bool isT0 = arb.tokenIn == token0;
        // debtToken = tokenIn, debtAmount = A needed to get `borrowed` B from pool
        uint256 debtAmount = isT0
            ? Helper.getAmountInV2(borrowed, r0, r1)
            : Helper.getAmountInV2(borrowed, r1, r0);
        Helper._safeTransfer(arb.tokenIn, msg.sender, debtAmount);        
    }

    function uniswapV3SwapCallback(int256 a0, int256 a1, bytes calldata data) external {
        if (msg.sender != _expectedCallback) revert Auth();

        uint8 mode = abi.decode(data, (uint8));
        if (mode == 1) {
            (, address tokenIn, ) = abi.decode(data, (uint8, address, address));
            bool is0 = a0 > 0;
            address req  = is0 ? Helper._token0(msg.sender) : Helper._token1(msg.sender);
            uint256 need = is0 ? uint256(a0) : uint256(a1);
            if (req != tokenIn) revert ModePathMismatch();
            Helper._safeTransfer(req, msg.sender, need);
            return;
        }

        _expectedCallback = address(0);
        // data = uint8(2) ++ abi.encode(Data, borrowAmt)
        // Skip the first byte (mode discriminator) and decode the rest
        (, Data memory arb,) = abi.decode(data, (uint8, Data, uint256));

        bool borrowedIs0 = a0 < 0;
        uint256 borrowed = borrowedIs0 ? uint256(-a0) : uint256(-a1);        address t0 = Helper._token0(msg.sender);
        address t1 = Helper._token1(msg.sender);
        address debtToken = borrowedIs0 ? t1 : t0;

        if (debtToken != arb.tokens[arb.tokens.length - 1]) revert ModePathMismatch();

        _execute(arb, borrowed, 1, 1);

        if (a0 > 0) {
            uint256 owe0 = uint256(a0);
            Helper._safeTransfer(t0, msg.sender, owe0);
        }
        if (a1 > 0) {
            uint256 owe1 = uint256(a1);
            Helper._safeTransfer(t1, msg.sender, owe1);
        }
    }

    function _execute(Data memory arb, uint256 borrowed, uint256 startPoolIdx, uint256 startTokenIdx) internal {
        address curToken = arb.tokens[startTokenIdx];
        uint256 amt = borrowed;
        uint256 hopIdx = startTokenIdx;
        for (uint i = startPoolIdx; i < arb.pools.length; ) {
            address nextToken = arb.tokens[hopIdx + 1];
            amt = _swap(arb.pools[i], curToken, nextToken, amt);
            curToken = nextToken;
            unchecked { ++i; ++hopIdx; }
        }
    }

    function _swap(address pool, address tokenIn, address tokenOut, uint256 amountIn) internal returns (uint256 out) {
        if (Helper._isUniswapV3(pool)) {
            bool z = (tokenIn == Helper._token0(pool));
            uint160 sqrtLimit = z ? 4295128740 : 1461446703485210103287273052203988822378723970341;
            _expectedCallback = pool;
            (int256 a0, int256 a1) = IUniswapV3Pool(pool).swap(address(this), z, int256(amountIn), sqrtLimit, abi.encode(uint8(1), tokenIn, tokenOut));
            _expectedCallback = address(0);
            return z ? uint256(-a1) : uint256(-a0);
        }

        IUniswapV2Pair p2 = IUniswapV2Pair(pool);
        (uint112 r0, uint112 r1,) = p2.getReserves();
        address t0 = Helper._token0(pool);
        bool isT0 = tokenIn == t0;
        out = isT0 ? Helper.getAmountOutV2(amountIn, r0, r1) : Helper.getAmountOutV2(amountIn, r1, r0);
        Helper._safeTransfer(tokenIn, pool, amountIn);
        bool outIsT0 = tokenOut == t0;
        p2.swap(outIsT0 ? out : 0, outIsT0 ? 0 : out, address(this), "");
    }

    function _processProfit(Data memory arb, uint256 startBalance, uint256 builderFeeBps) internal {
        if (arb.tokenIn == address(0)) return;
        uint256 endBalance = Helper._balanceOf(arb.tokenIn, address(this));
        if (endBalance <= startBalance) revert NoProfit();
        uint256 profit = endBalance - startBalance;
        if (profit < arb.minProfit) revert NoProfit();
        emit DONE(arb.tokenIn, profit);
        if (arb.tokenIn == WETH) {
            IWETH(WETH).withdraw(profit);
            address _owner = owner();

            uint256 builderTip = (profit * builderFeeBps) / 10000;
            uint256 ownerProfit = profit - builderTip;
            // pay builder
            assembly {
                let ok := call(gas(), coinbase(), builderTip, 0, 0, 0, 0)
                if iszero(ok) {
                    mstore(0x00, 0x90b8ec18) // TransferFailed()
                    revert(0x1c, 0x04)
                }
            }
            // pay owner
            assembly {
                let ok := call(gas(), _owner, ownerProfit, 0, 0, 0, 0)
                if iszero(ok) {
                    mstore(0x00, 0x90b8ec18) // TransferFailed()
                    revert(0x1c, 0x04)
                }
            }
        } else {
            Helper._safeTransfer(arb.tokenIn, owner(), profit);
        }
    }

    function yieldOut(Data memory arb)
        public
        view
        returns (Data memory ad, uint256 profit)
    {
        ad = _determineBorrow(arb);
        require(ad.amountIn > 0, "no arb");
        require(ad.pools.length == ad.tokens.length - 1, "invalid pools/tokens length");
        require(ad.pools.length == ad.fees.length, "pools/fees mismatch");

        uint256 current = ad.amountIn;
        uint256 startIdx = ad.mode == 1 ? 1 : 0;

        for (uint256 i = startIdx; i < ad.pools.length; ) {
            address pool    = ad.pools[i];
            address tokenIn = ad.tokens[i];
            address tOut    = ad.tokens[i + 1];
            if (Helper._isUniswapV3(pool)) {
                uint24 fee = ad.fees.length > i ? ad.fees[i] : 3000;
                (current,,,) = IQuoter(Quoter).quoteExactInputSingle(
                    IQuoter.QuoteExactInputSingleParams({
                        tokenIn: tokenIn, tokenOut: tOut, amountIn: current,
                        fee: fee, sqrtPriceLimitX96: 0
                    })
                );
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool).getReserves();
                current = tokenIn == Helper._token0(pool)
                    ? Helper.getAmountOutV2(current, r0, r1)
                    : Helper.getAmountOutV2(current, r1, r0);
            }
            unchecked { ++i; }
        }

        if (ad.mode == 0) {
            profit = current > ad.amountIn ? current - ad.amountIn : 0;
        } else {
            uint256 debtAmount;
            address pool0 = ad.pools[0];
            if (Helper._isUniswapV3(pool0)) {
                (debtAmount,,,) = IQuoter(Quoter).quoteExactOutputSingle(
                    IQuoter.QuoteExactOutputSingleParams({
                        tokenIn: ad.tokens[0], tokenOut: ad.tokens[1],
                        amount: ad.amountIn, fee: ad.fees[0], sqrtPriceLimitX96: 0
                    })
                );
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool0).getReserves();
                debtAmount = ad.tokens[0] == Helper._token0(pool0)
                    ? Helper.getAmountInV2(ad.amountIn, r0, r1)
                    : Helper.getAmountInV2(ad.amountIn, r1, r0);
            }
            profit = current > debtAmount ? current - debtAmount : 0;
        }
        return (ad, profit);
    }

    function withdraw(address token, uint256 amount) external onlyOwner {
        if (token == address(0)) {
            address _owner = owner();
            assembly {
                let ok := call(gas(), _owner, selfbalance(), 0, 0, 0, 0)
                if iszero(ok) {
                    mstore(0x00, 0x90b8ec18) // TransferFailed()
                    revert(0x1c, 0x04)
                }
            }
        } else {
            uint256 bal = Helper._balanceOf(token, address(this));
            if (amount != 0) {
                require(bal >= amount, "insuf bal");
                Helper._safeTransfer(token, owner(), amount);
            } else {
                Helper._safeTransfer(token, owner(), bal);
            }
        }
    }
}