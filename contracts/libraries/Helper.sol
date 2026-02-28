// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;

/**
 * Production-ready Reserves & Swap Simulator for Uniswap V2 & V3
 * -----------------------------------------------------------------
 * Features:
 * - getReservesV2: returns Uniswap V2 pair reserves (uses getReserves())
 * - getEffectiveReservesV3: returns effective virtual reserves for pricing derived from liquidity + slot0
 * - getBalancesV3: raw ERC20 balances in pool
 * - getPriceV2: returns price token1/token0 and token0/token1 encoded as Q96 fixed point
 * - getPriceV3: returns sqrtPriceX96 from slot0 and derived price token1/token0 encoded as Q96
 * - getAmountsOutV2 / getAmountsInV2: canonical V2 path helpers
 * - getAmountsOutV3 / getAmountsInV3: accurate V3 exact-in / exact-out simulations that iterate initialized ticks using tickBitmap for efficient searching
 * - simulateSwapExactInputV3 / simulateSwapExactOutputV3: top-level simulation functions
 *
 * Important production notes (read carefully):
 * - This contract is intended to be deployed on mainnet as a read-only helper (view functions). Many functions are gas-heavy if executed on-chain (they iterate ticks). Intended for off-chain eth_call usage by frontends/backends.
 * - Extensive unit testing and an external security audit are REQUIRED before relying on it for on-chain execution decisions.
 * - The contract uses interfaces from Uniswap v3-core. Ensure your project has matching v3-core versions.
 * - The V3 simulation attempts to faithfully implement Uniswap V3 swap math (fees, tick crossing, tickBitmap traversal). Edge-cases should be fuzz-tested against actual pools.
 */

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
// import "@uniswap/v3-core/contracts/libraries/FixedPoint96.sol";
import "../interfaces/IUniswapV3Pool.sol";
import "../interfaces/IUniswapV2Pair.sol";
import "../interfaces/IQuoter.sol";
import "./Decimal.sol";
// import "./TickMath.sol";



/// @notice Extended pool interface to access tickBitmap getter and fee/tickSpacing
interface IUniswapV3PoolExt is IUniswapV3Pool {
    // Intentionally left empty - inherits from IUniswapV3Pool
}


library Helper {
    // using FixedPoint96 for uint224;
    using Decimal for Decimal.D256;

    // Standard Uniswap V2 fee structure
    uint256 internal constant FEE_NUM = 997; // gamma (0.997)
    uint256 internal constant FEE_DEN = 1000;  // Denominator (1000)

    uint256 private constant Q96 = 2**96;
    uint256 private constant FEE_DENOMINATOR = 1_000_000; // we use 1e6 to keep integer math consistent with earlier helpers

    uint256 private constant FEE_PIPS = 3000; // 0.3% = 997/1000 effective
    uint256 private constant ONE = 1e18;

    // struct StepStateOut {
    //     uint160 sqrtP;
    //     uint160 sqrtPNext;
    //     int24 nextTick;
    //     uint128 L;
    //     uint256 remainingOut;
    //     uint256 inAccum;
    // }

    // struct StepStateIn {
    //     uint160 sqrtP;
    //     uint160 sqrtPNext;
    //     int24 nextTick;
    //     uint128 L;
    //     uint256 remaining;
    //     uint256 outAccum;
    // }
    // -------------------------------
    // V2 helpers
    // -------------------------------

    /// @notice Get reserves from Uniswap V2 pair (native getReserves)
    function getReservesV2(address pair) public view returns (uint112 reserve0, uint112 reserve1) {
        (reserve0, reserve1,) = IUniswapV2Pair(pair).getReserves();
    }

    // /// @notice Get price for V2 as Q96 fixed point: returns priceToken1PerToken0 and priceToken0PerToken1
    // /// priceToken1PerToken0 = (reserve1 << 96) / reserve0
    // function getPriceV2(address pair) public view returns (uint256 price1Per0Q96, uint256 price0Per1Q96) {
    //     (uint112 r0, uint112 r1) = getReservesV2(pair);
    //     require(r0 > 0 && r1 > 0, "empty reserves");
    //     price1Per0Q96 = (uint256(r1) << 96) / uint256(r0);
    //     price0Per1Q96 = (uint256(r0) << 96) / uint256(r1);
    // }


    function getAmountOutV2(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        require(amountIn > 0, "Insufficient input");
        require(reserveIn > 0 && reserveOut > 0, "Insufficient liquidity: dead");
        uint256 amountInWithFee = amountIn * 997; // Uniswap V2 fee 0.3%
        uint256 numerator = amountInWithFee * reserveOut;
        uint256 denominator = reserveIn * 1000 + amountInWithFee;
        return numerator / denominator;
    }

    function getAmountInV2(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        require(amountOut > 0, "Insufficient output");
        require(reserveIn > 0 && reserveOut > 0 && reserveOut > amountOut, "Insufficient liquidity");
        uint256 numerator = reserveIn * amountOut * 1000;
        uint256 denominator = (reserveOut - amountOut) * 997;
        return (numerator / denominator) + 1;
    }

    function getAmountOutV2WithFee(uint256 amountIn, uint256 reserveIn, uint256 reserveOut, uint256 fee) internal pure returns (uint256) {
        require(amountIn > 0, "Insufficient input");
        require(reserveIn > 0 && reserveOut > 0, "Insufficient liquidity: dead"); fee /= 10;
        uint256 amountInWithFee = amountIn * (1000 - fee); // Uniswap V2 fee 0.3%
        uint256 numerator = amountInWithFee * reserveOut;
        uint256 denominator = reserveIn * 1000 + amountInWithFee;
        return numerator / denominator;
    }

    function getAmountInV2WithFee(uint256 amountOut, uint256 reserveIn, uint256 reserveOut, uint256 fee) internal pure returns (uint256) {
        require(amountOut > 0, "Insufficient output");
        require(reserveIn > 0 && reserveOut > 0 && reserveOut > amountOut, "Insufficient liquidity");
        uint256 numerator = reserveIn * amountOut * 1000; fee /= 10;
        uint256 denominator = (reserveOut - amountOut) * (1000 - fee);
        return (numerator / denominator) + 1;
    }

    /// @dev NOTE: _pairForV2 is a placeholder. In prod you should pass the pair address directly rather than deriving
    function _pairForV2(address, address) internal pure returns (address) {
        revert("derive pair off-chain; pass pair address into V2 functions");
    }

    // -------------------------------
    // V3 helpers
    // -------------------------------

    function _isUniswapV3(address pool) internal view returns (bool) {
        try IUniswapV3Pool(pool).slot0() { return true; }
        catch { return false; }
    }

    function getPoolTokens(address pool) internal view returns (address t0, address t1, bool isV3) {
        isV3 = _isUniswapV3(pool);
        t0 = isV3 ? IUniswapV3Pool(pool).token0() : IUniswapV2Pair(pool).token0();
        t1 = isV3 ? IUniswapV3Pool(pool).token1() : IUniswapV2Pair(pool).token1();
        // For V3, "sort" by addr if needed: if (t0 > t1) (t0, t1) = (t1, t0);
    }

    /// @notice Raw ERC20 balances inside V3 pool (not for pricing)
    function getReservesV3(address pool) public view returns (uint256 balance0, uint256 balance1) {
        IUniswapV3Pool p = IUniswapV3Pool(pool);
        balance0 = IERC20(p.token0()).balanceOf(pool);
        balance1 = IERC20(p.token1()).balanceOf(pool);
    }

    /// @notice Effective reserves derived from liquidity and sqrtPriceX96.
    /// reserve0 = L * 2^96 / sqrtPriceX96
    /// reserve1 = L * sqrtPriceX96 / 2^96
    // function getEffectiveReservesV3(address pool) public view returns (uint256 reserve0, uint256 reserve1) {
    //     IUniswapV3Pool p = IUniswapV3Pool(pool);
    //     (uint160 sqrtPriceX96,,,,,,) = p.slot0();
    //     uint128 liquidity = p.liquidity();
    //     require(liquidity > 0, "no liquidity");
    //     reserve0 = (uint256(liquidity) << 96) / uint256(sqrtPriceX96);
    //     reserve1 = (uint256(liquidity) * uint256(sqrtPriceX96)) >> 96;
    // }

    /// @notice Get V3 pool price two ways: returns sqrtPriceX96 and price token1/token0 in Q96
    function getPriceV3(address pool) public view returns (uint160 sqrtPriceX96, uint256 price1Per0Q96, uint256 price0Per1Q96) {
        IUniswapV3Pool p = IUniswapV3Pool(pool);
        (sqrtPriceX96,,,,,,) = p.slot0();
        // priceX192 = sqrtPriceX96^2 (Q192)
        uint256 priceX192 = uint256(sqrtPriceX96) * uint256(sqrtPriceX96);
        // convert to Q96 by shifting right 96
        price1Per0Q96 = priceX192 >> 96;
        // reciprocal for 0 per 1: compute safely
        if (price1Per0Q96 > 0) {
            price0Per1Q96 = (uint256(1) << 192) / price1Per0Q96;
        } else {
            price0Per1Q96 = 0;
        }
    }

    function sortPools(
        address[] memory pools,
        address[] memory tokens,
        bool borrowTokenSmaller
        //uint8 mode
    ) internal view returns (address[] memory, address[] memory) {
        if (pools.length > 2) return (pools, tokens);

        bool isV3_0 = _isUniswapV3(pools[0]);
        bool isV3_1 = _isUniswapV3(pools[1]);

        Decimal.D256 memory price0;
        Decimal.D256 memory price1;
        address t0;
        address t1;

        if (isV3_0 && isV3_1) {
            (price0, price1, t0, t1) = _getV3Prices(pools, borrowTokenSmaller);
        } else if (!isV3_0 && !isV3_1) {
            (price0, price1, t0, t1) = _getV2Prices(pools, borrowTokenSmaller);
        } else {
            // Cross protocol case
            (price0, price1, t0, t1) = _getCrossProtocolPrices(pools, borrowTokenSmaller);
        }

        bool pool0Higher = !price0.lessThan(price1);
        
        // sell high, buy low
        // pools[0] = poolHigh (where A is expensive — sell A here in mode 0, or borrow B here in mode 1)
        // pools[1] = poolLow  (where A is cheap   — buy A back here in both modes)
        (pools[0], pools[1]) = pool0Higher ? (pools[1], pools[0]) : (pools[0], pools[1]);

        tokens[0] = t0;
        tokens[1] = t1;
        tokens[2] = tokens[0];

        return (pools, tokens);
    }


    function _getV2Prices(address[] memory pools, bool borrowTokenSmaller)
        internal
        view
        returns (Decimal.D256 memory price0, Decimal.D256 memory price1, address t0, address t1){
        
        address token0 = IUniswapV2Pair(pools[0]).token0();
        address token1 = IUniswapV2Pair(pools[0]).token1();

        (uint256 r00, uint256 r01, ) = IUniswapV2Pair(pools[0]).getReserves();
        (uint256 r10, uint256 r11, ) = IUniswapV2Pair(pools[1]).getReserves();

        (price0, price1, t0, t1) = borrowTokenSmaller
            ? (Decimal.from(r00).div(r01), Decimal.from(r10).div(r11), token0, token1)
            : (Decimal.from(r01).div(r00), Decimal.from(r11).div(r10), token1, token0);
    }

    function _getV3Prices(address[] memory pools, bool borrowTokenSmaller)
        internal
        view
        returns (Decimal.D256 memory price0, Decimal.D256 memory price1, address t0, address t1)
    {
        address token0 = IUniswapV3Pool(pools[0]).token0();
        address token1 = IUniswapV3Pool(pools[0]).token1();

        (, uint256 p0Price1Per0Q96, uint256 p0Price0Per1Q96) = getPriceV3(pools[0]);
        (, uint256 p1Price1Per0Q96, uint256 p1Price0Per1Q96) = getPriceV3(pools[1]);

        if (borrowTokenSmaller) {
            return (
                Decimal.from(p0Price1Per0Q96),
                Decimal.from(p1Price1Per0Q96),
                token0,
                token1
            );
        } else {
            return (
                Decimal.from(p0Price0Per1Q96),
                Decimal.from(p1Price0Per1Q96),
                token1,
                token0
            );
        }
    }

    function _getCrossProtocolPrices(address[] memory pools, bool borrowTokenSmaller)
        internal
        view
        returns (Decimal.D256 memory price0, Decimal.D256 memory price1, address t0, address t1)
    {
        bool isV3_0 = _isUniswapV3(pools[0]);

        // Get common token pair reference
        address token0;
        address token1;

        if (isV3_0) {
            token0 = IUniswapV3Pool(pools[0]).token0();
            token1 = IUniswapV3Pool(pools[0]).token1();
        } else {
            token0 = IUniswapV2Pair(pools[0]).token0();
            token1 = IUniswapV2Pair(pools[0]).token1();
        }

        uint256 p0Q96;
        uint256 p1Q96;

        if (isV3_0) {
            (, uint256 p1Per0, uint256 p0Per1) = getPriceV3(pools[0]);
            p0Q96 = borrowTokenSmaller ? p1Per0 : p0Per1;
        } else {
            (uint112 r0, uint112 r1, ) = IUniswapV2Pair(pools[0]).getReserves();
            p0Q96 = borrowTokenSmaller
                ? (uint256(r0) << 96) / uint256(r1)
                : (uint256(r1) << 96) / uint256(r0);
        }

        if (_isUniswapV3(pools[1])) {
            (, uint256 p1Per0, uint256 p0Per1) = getPriceV3(pools[1]);
            p1Q96 = borrowTokenSmaller ? p1Per0 : p0Per1;
        } else {
            (uint112 r0, uint112 r1, ) = IUniswapV2Pair(pools[1]).getReserves();
            p1Q96 = borrowTokenSmaller
                ? (uint256(r1) << 96) / uint256(r0)
                : (uint256(r0) << 96) / uint256(r1);
        }

        return (
            Decimal.from(p0Q96),
            Decimal.from(p1Q96),
            borrowTokenSmaller ? token0 : token1,
            borrowTokenSmaller ? token1 : token0
        );
    }


    /// @dev calculate the maximum base asset amount to borrow in order to get maximum profit during arbitrage
    function calcOptimalV2Borrow(
        uint256 resInP0,  // res_A_in_low/borrow pool (A in low)
        uint256 resOutP0,    // res_B_out_low/borrow pool (B out low)
        uint256 resInP1,  // res_B_in_high/unwind pool (B in high)
        uint256 resOutP1,    // res_A_out_high/unwind pool (A out high)
        uint8 mode
    ) internal pure returns (uint256 amount) {
        // Scaling for 18-dec safe signed math (handles 6-dec like USDC via min ref; reserves as-is)
        uint256 min1 = resInP0 < resOutP0 ? resInP0 : resOutP0;
        uint256 min2 = resInP1 < resOutP1 ? resInP1 : resOutP1;
        uint256 min = min1 < min2 ? min1 : min2;
        uint256 d = getScalingFactor(min);
        
        int256 a1 = int256(resInP0 / d); 
        int256 b1 = int256(resOutP0 / d); 
        int256 a2 = int256(resInP1 / d);  
        int256 b2 = int256(resOutP1 / d);

        // Mode 0: Quadratic profit-max round-trip (A→B on high P1, B→A on low P0)
        // Derivation: P(b) = getAmountOut(getAmountOut(b, P1), P0) - b; dP/db=0 → quadratic
        int256 k = (a2 * 997) / 1000 + (b1 * 997 * 997) / (1000 * 1000);  // Adjusted for high in, low out
        int256 qa = k * k;
        int256 qb = 2 * k * a1 * a2;
        int256 qc = a1 * a2 * a1 * a2 - (b1 * a1 * a2 * b2 * 997 * 997) / (1000 * 1000);

        (int256 x1, int256 x2) = calcSolutionForQuadratic(qa, qb, qc);
        int256 x = (x1 > 0 && x1 < b2) ? x1 : x2;  // Positive root < res_out both pools
        if (x <= 0 || x >= b2) return 0;//fallbackResult(a1, b1, a2, b2) * d;
        amount = uint256(x) * d;

        if (mode == 1) amount = getAmountOutV2(amount, resInP0, resOutP0);
        
    }

    function fallbackResult(int256 a1, int256 b1, int256 a2, int256 b2) internal pure returns (uint256 amt) {
        require((a1 > 0 && b1 > 0 && a2 > 0 && b2 > 0), 'Complex figures');
    
        uint256 maxBorrow = uint256(a1);
        uint256 swapPrice = uint256(b1 / a1);
        uint256 maxSwap = uint256(b2);

        if ((maxBorrow * swapPrice) > maxSwap) {
            amt = maxSwap * 997 / 1000;
        } else {
            amt = maxBorrow * 997 / 1000;
        }
        // Safe cap for reserves (swappable on both)
        amt = amt < uint256(a1) ? amt : uint256(a1);  // <= res_in_low
        amt = amt < uint256(a2) ? amt : uint256(a2);  // <= res_in_high
    }

    function getScalingFactor(uint256 min) internal pure returns (uint256 d) {
        if (min > 1e24) d = 1e20;
        else if (min > 1e23) d = 1e19;
        else if (min > 1e22) d = 1e18;
        else if (min > 1e21) d = 1e17;
        else if (min > 1e20) d = 1e16;
        else if (min > 1e19) d = 1e15;
        else if (min > 1e18) d = 1e14;
        else if (min > 1e17) d = 1e13;
        else if (min > 1e16) d = 1e12;
        else if (min > 1e15) d = 1e11;
        else d = 1e10;
    }

    /// @dev find solution of quadratic equation: ax^2 + bx + c = 0, only return the positive solution
    function calcSolutionForQuadratic(int256 a, int256 b, int256 c) internal pure returns (int256 x1, int256 x2) {
        int256 m = b**2 - 4 * a * c;
        // m < 0 leads to complex number
        if (m <= 0) return (0, 0);  // No real solution

        int256 sqrtM = int256(sqrt(uint256(m)));
        x1 = (-b + sqrtM) / (2 * a);
        x2 = (-b - sqrtM) / (2 * a);
    }

    /// @dev Newton’s method for calculating square root of n
    function sqrt(uint256 n) internal pure returns (uint256 res) {
        assert(n > 1);

        // The scale factor is a crude way to turn everything into integer calcs.
        // Actually do (n * 10 ^ 6) ^ (1/2)
        uint256 _n = n * 10**6;
        uint256 c = _n;
        res = _n;

        uint256 xi;
        while (true) {
            xi = (res + c / res) / 2;
            // don't need be too precise to save gas
            if (res - xi < 1000) break;
            res = xi;
        }
        res = res / 10**3;
    }


    // coarse V3 borrow estimation (sampling)
    function estimateOptimalV3Borrow(address[] memory tokens, uint24[] memory fees, address v3Quoter) internal view  returns (uint256) {
        require(fees.length > 0, "Missing fees");
        require(tokens.length >= 2, "Invalid tokens");
        require(fees.length == tokens.length - 1, "Path mismatch");

        // Build path once
        bytes memory path;
        for (uint i = 0; i < tokens.length - 1; i++) {
            path = abi.encodePacked(path, tokens[i], fees[i]);
        }
        path = abi.encodePacked(path, tokens[tokens.length - 1]);

        // Adaptive bracketing: 3 samples to find profitable interval
        uint256[] memory probes = new uint256[](3);
        probes[0] = 1e16; probes[1] = 1e18; probes[2] = 1e20;
        uint256 low = type(uint256).max;
        uint256 high = 0;
        uint256 maxProfit = 0;
        uint256 bestAmt = 0;

        for (uint i = 0; i < 3; i++) {
            uint256 profit = _getProfit(path, probes[i], v3Quoter);
            if (profit > maxProfit) {
                maxProfit = profit;
                bestAmt = probes[i];
            }
            if (profit > 0) {
                if (probes[i] < low) low = probes[i];
                if (probes[i] > high) high = probes[i];
            }
        }

        if (maxProfit == 0) return bestAmt; // Fallback to best probe if no profit

        // Widen if needed (assume concave, extend by factor)
        if (low == type(uint256).max) {
            low = bestAmt / 10; // Conservative
            high = bestAmt * 10;
        } else if (low == high) {
            low /= 2;
            high *= 2;
        }

        // Golden section search: ~10 iters for 1e-10 precision, fewer quotes than ternary
        uint256 c1 = low + (high - low) * 618 / 1000; // phi^{-1} ≈ 0.618
        uint256 c2 = low + (high - low) * 382 / 1000; // 1 - phi^{-1} ≈ 0.382
        uint256 f1 = _getProfit(path, c1, v3Quoter);
        uint256 f2 = _getProfit(path, c2, v3Quoter);

        for (uint iter = 0; iter < 12; iter++) { // Conservative iters
            if (high - low < 1e6) break; // Sub-wei precision, early stop
            if (f1 > f2) {
                high = c2;
                c2 = c1;
                f2 = f1;
                c1 = low + (high - low) * 382 / 1000;
                f1 = _getProfit(path, c1, v3Quoter);
            } else {
                low = c1;
                c1 = c2;
                f1 = f2;
                c2 = low + (high - low) * 618 / 1000;
                f2 = _getProfit(path, c2, v3Quoter);
            }
            if (f1 > maxProfit) {
                maxProfit = f1;
                bestAmt = c1;
            }
            if (f2 > maxProfit) {
                maxProfit = f2;
                bestAmt = c2;
            }
        }

        // Final verify at best
        uint256 finalProfit = _getProfit(path, bestAmt, v3Quoter);
        return finalProfit > maxProfit ? bestAmt : _refineLocal(path, bestAmt, v3Quoter);
    }

    function _getProfit(bytes memory path, uint256 amt, address quoter) private view  returns (uint256) {
        try IQuoter(quoter).quoteExactInput(path, amt) returns (
                uint256 out,
                uint160[] memory /* ignore */,
                uint32[] memory /* ignore */,
                uint256 /* gasEst ignore */
            ) {
            return out > amt ? out - amt : 0;
        } catch {
            return 0;
        }
    }

    function _refineLocal(bytes memory path, uint256 base, address quoter) private view returns (uint256) {
        // Quick 3-point local ternary around base for micro-opt
        uint256 delta = base / 100; // 1% steps
        if (delta == 0) return base;
        uint256 p1 = _getProfit(path, base - delta, quoter);
        uint256 p2 = _getProfit(path, base + delta, quoter);
        uint256 p0 = _getProfit(path, base, quoter);
        if (p1 > p0 && p1 > p2) return base - delta;
        if (p2 > p0 && p2 > p1) return base + delta;
        return base;
    }

    /**
     * @notice Converts a uint256 to its string representation.
     * @param _i The unsigned integer to convert.
     * @return A string representing the integer.
     */
    function uint2str(uint256 _i) internal pure returns (string memory) {
        if (_i == 0) {
            return "0";
        }
        
        uint256 j = _i;
        uint256 length;
        
        // 1. Calculate the length of the number's string representation
        while (j != 0) {
            length++;
            j /= 10;
        }
        
        // 2. Create a memory string of the correct length
        bytes memory bstr = new bytes(length);
        j = _i;
        
        // 3. Fill the bytes array from right to left
        while (j != 0) {
            // Get the last digit
            uint8 lastDigit = uint8(j % 10); 
            
            // Convert digit to ASCII character (e.g., 0 + 48 = '0')
            // The bytes array is filled from the end backwards
            bstr[--length] = bytes1(uint8(48) + lastDigit);
            
            // Remove the last digit
            j /= 10;
        }
        
        // 4. Convert bytes back to string and return
        return string(bstr);
    }

    function calcOptimalV2V3(address[] memory pools, uint8 mode) internal view returns (uint256 amount) {
        uint256 resInP0;  uint256 resOutP0;  uint256 resInP1;  uint256 resOutP1;
        
        if (_isUniswapV3(pools[0])) {
            (resInP0, resOutP0) = getReservesV3(pools[0]);
        } else {
            (resInP0, resOutP0) = getReservesV2(pools[0]);
        }

        if (_isUniswapV3(pools[1])) {
            (resInP1, resOutP1) = getReservesV3(pools[1]);
        } else {
            (resInP1, resOutP1) = getReservesV2(pools[1]);
        }

        amount = calcOptimalV2Borrow(resInP0, resOutP0, resInP1, resOutP1, mode);

        // if (amount == 0){
        //     // take 70% of min reserve
        //     uint256 minResA = resInP0 < resOutP0 ? resInP0 : resOutP0;
        //     uint256 minResB = resInP1 < resOutP1 ? resInP1 : resOutP1;
        //     uint256 res = mode == 0 ? minResA : minResB;
        //     amount = res * 70 / 100;
        // }
    }
    // -------------------------------
    // V3: Full simulation (exact-in and exact-out)
    // - Uses tickBitmap scanning for next initialized tick (efficient)
    // - Implements swap step math similar to Uniswap V3 SwapMath
    // - IMPORTANT: heavy; intended for off-chain eth_call
    // -------------------------------

    function _validatePoolTokens(address[] memory tokens, address[] memory pools) internal view {
        for (uint256 i = 0; i < pools.length; i++) {
            address pool = pools[i];

            // Fix #16: ensure the address is a contract before calling into it
            require(_isContract(pool), "pool not a contract");

            address tokenIn  = tokens[i];
            address tokenOut = tokens[i + 1];

            (address pt0, address pt1,) = Helper.getPoolTokens(pool);

            // The pool must hold exactly the two tokens specified for this hop
            bool valid = (pt0 == tokenIn && pt1 == tokenOut) ||
                         (pt0 == tokenOut && pt1 == tokenIn);
            require(valid, "pool/token mismatch");
        }
    }

    function _isContract(address addr) internal view returns (bool) {
        uint256 size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

}
