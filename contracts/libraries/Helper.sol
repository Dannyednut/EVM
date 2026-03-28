// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "../interfaces/IUniswapV3Pool.sol";
import "../interfaces/IUniswapV2Pair.sol";
import "../interfaces/IQuoter.sol";
import "./Decimal.sol";

library Helper {
    using Decimal for Decimal.D256;

    uint256 private constant Q96 = 2**96;

    // -------------------------------------------------------------------------
    // V2 math
    // -------------------------------------------------------------------------

    function getAmountOutV2(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256) {
        require(amountIn > 0, "amt");
        require(reserveIn > 0 && reserveOut > 0, "liq");
        uint256 amountInWithFee = amountIn * 997;
        uint256 numerator       = amountInWithFee * reserveOut;
        uint256 denominator     = reserveIn * 1000 + amountInWithFee;
        return numerator / denominator;
    }

    function getAmountInV2(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256) {
        require(amountOut > 0, "amt");
        require(reserveIn > 0 && reserveOut > amountOut, "liq");
        uint256 numerator   = reserveIn * amountOut * 1000;
        uint256 denominator = (reserveOut - amountOut) * 997;
        return (numerator / denominator) + 1;
    }

    function getAmountOutV2WithFee(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut,
        uint24  fee        // pip format: 3000 = 0.3%, 500 = 0.05%
    ) internal pure returns (uint256) {
        require(amountIn > 0, "amt");
        require(reserveIn > 0 && reserveOut > 0, "liq");
        uint256 g               = 1e6 - uint256(fee);   // e.g. 997000 for 0.3%
        uint256 amountInWithFee = amountIn * g;
        uint256 numerator       = amountInWithFee * reserveOut;
        uint256 denominator     = reserveIn * 1e6 + amountInWithFee;
        return numerator / denominator;
    }

    function getAmountInV2WithFee(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut,
        uint24  fee
    ) internal pure returns (uint256) {
        require(amountOut > 0, "amt");
        require(reserveIn > 0 && reserveOut > amountOut, "liq");
        uint256 g           = 1e6 - uint256(fee);
        uint256 numerator   = reserveIn * amountOut * 1e6;
        uint256 denominator = (reserveOut - amountOut) * g;
        return (numerator / denominator) + 1;
    }

    // -------------------------------------------------------------------------
    // Pool detection & token resolution
    // -------------------------------------------------------------------------

    function _isUniswapV3(address pool) internal view returns (bool) {
        try IUniswapV3Pool(pool).slot0() { return true; }
        catch { return false; }
    }

    function _isContract(address addr) internal view returns (bool) {
        uint256 size;
        assembly { size := extcodesize(addr) }
        return size > 0;
    }

    function getPoolTokens(address pool)
        internal view
        returns (address t0, address t1, bool isV3)
    {
        isV3 = _isUniswapV3(pool);
        t0   = isV3 ? IUniswapV3Pool(pool).token0() : IUniswapV2Pair(pool).token0();
        t1   = isV3 ? IUniswapV3Pool(pool).token1() : IUniswapV2Pair(pool).token1();
    }

    // -------------------------------------------------------------------------
    // Reserve helpers
    // -------------------------------------------------------------------------

    function getReservesV2(address pair)
        internal view
        returns (uint256 reserve0, uint256 reserve1)
    {
        (uint112 r0, uint112 r1,) = IUniswapV2Pair(pair).getReserves();
        reserve0 = uint256(r0);
        reserve1 = uint256(r1);
    }

    /// @dev Virtual reserves derived from L and sqrtPriceX96.
    ///      reserve0 = L * 2^96 / sqrtPriceX96
    ///      reserve1 = L * sqrtPriceX96 / 2^96
    ///      Accurate within the current tick; approximation across tick boundaries.
    function getEffectiveReservesV3(address pool)
        internal view
        returns (uint256 reserve0, uint256 reserve1)
    {
        (uint160 sqrtPriceX96,,,,,,) = IUniswapV3Pool(pool).slot0();
        uint128 L = IUniswapV3Pool(pool).liquidity();
        require(L > 0, "no liq");
        reserve0 = (uint256(L) << 96) / uint256(sqrtPriceX96);
        reserve1 = (uint256(L) * uint256(sqrtPriceX96)) >> 96;
    }

    /// @dev Returns (resIn, resOut) for a pool ordered by trade direction.
    ///      For V3 uses effective virtual reserves; for V2 uses real reserves.
    ///      tokenIn must be one of the pool's two tokens.
    function _getOrderedReserves(address pool, address tokenIn)
        internal view
        returns (uint256 resIn, uint256 resOut)
    {
        uint256 r0; uint256 r1; address t0;
        if (_isUniswapV3(pool)) {
            (r0, r1)  = getEffectiveReservesV3(pool);
            t0        = IUniswapV3Pool(pool).token0();
        } else {
            (r0, r1)  = getReservesV2(pool);
            t0        = IUniswapV2Pair(pool).token0();
        }
        (resIn, resOut) = tokenIn == t0 ? (r0, r1) : (r1, r0);
    }

    // -------------------------------------------------------------------------
    // Pool sorting
    // -------------------------------------------------------------------------

    /// @dev Sorts two pools so pools[0] is the borrow pool (lower price of tokenIn)
    ///      and pools[1] is the unwind pool (higher price of tokenIn).
    ///      Only operates on 2-pool paths; passes through longer paths unchanged.
    function sortPools(
        address[] memory pools,
        address[] memory tokens,
        uint24[] memory fees,
        bool borrowTokenSmaller
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
            (price0, price1, t0, t1) = _getCrossProtocolPrices(pools, borrowTokenSmaller);
        }

        bool pool0Lower = price0.lessThan(price1);
        // pools[0] = high price pool  (sell here — tokenIn is expensive)
        // pools[1] = low price pool (unwind here — tokenIn is cheap)
        if (pool0Lower) (pools[0], pools[1], fees[0], fees[1]) = (pools[1], pools[0], fees[1], fees[0]);

        tokens[0] = t0;
        tokens[1] = t1;
        tokens[2] = tokens[0]; // triangular: end token = start token

        return (pools, tokens);
    }

    function _getV2Prices(address[] memory pools, bool borrowTokenSmaller)
        internal view
        returns (
            Decimal.D256 memory price0,
            Decimal.D256 memory price1,
            address t0,
            address t1
        )
    {
        t0 = IUniswapV2Pair(pools[0]).token0();
        t1 = IUniswapV2Pair(pools[0]).token1();

        (uint256 r00, uint256 r01,) = IUniswapV2Pair(pools[0]).getReserves();
        (uint256 r10, uint256 r11,) = IUniswapV2Pair(pools[1]).getReserves();

        require(r00 > 0 && r01 > 0 && r10 > 0 && r11 > 0, "NO_LIQUIDITY");

        // ALWAYS token1 per token0
        Decimal.D256 memory p0_1per0 = Decimal.from(r01).div(r00);
        Decimal.D256 memory p1_1per0 = Decimal.from(r11).div(r10);

        Decimal.D256 memory p0_0per1 = Decimal.from(r00).div(r01);
        Decimal.D256 memory p1_0per1 = Decimal.from(r10).div(r11);

        (price0, price1, t0, t1) = borrowTokenSmaller
            ? (p0_1per0, p1_1per0, t0, t1)
            : (p0_0per1, p1_0per1, t1, t0);
    }

    function _getV3Prices(address[] memory pools, bool borrowTokenSmaller)
        internal view
        returns (
            Decimal.D256 memory price0,
            Decimal.D256 memory price1,
            address t0,
            address t1
        )
    {
        t0 = IUniswapV3Pool(pools[0]).token0();
        t1 = IUniswapV3Pool(pools[0]).token1();
        (, uint256 p0_1per0, uint256 p0_0per1) = _getPriceV3(pools[0]);
        (, uint256 p1_1per0, uint256 p1_0per1) = _getPriceV3(pools[1]);
        (price0, price1, t0, t1) = borrowTokenSmaller
            ? (Decimal.from(p0_1per0), Decimal.from(p1_1per0), t0, t1)
            : (Decimal.from(p0_0per1), Decimal.from(p1_0per1), t1, t0);
    }

    function _getCrossProtocolPrices(address[] memory pools, bool borrowTokenSmaller)
        internal view
        returns (
            Decimal.D256 memory price0,
            Decimal.D256 memory price1,
            address t0,
            address t1
        )
    {
        bool isV3_0 = _isUniswapV3(pools[0]);
        t0 = isV3_0 ? IUniswapV3Pool(pools[0]).token0() : IUniswapV2Pair(pools[0]).token0();
        t1 = isV3_0 ? IUniswapV3Pool(pools[0]).token1() : IUniswapV2Pair(pools[0]).token1();

        uint256 p0Q96 = _getPoolPriceQ96(pools[0], borrowTokenSmaller);
        uint256 p1Q96 = _getPoolPriceQ96(pools[1], borrowTokenSmaller);

        (price0, price1) = (Decimal.from(p0Q96), Decimal.from(p1Q96));
        (t0, t1) = borrowTokenSmaller ? (t0, t1) : (t1, t0);
    }

    function _getPoolPriceQ96(address pool, bool borrowTokenSmaller)
        private view
        returns (uint256)
    {
        if (_isUniswapV3(pool)) {
            (, uint256 p1Per0, uint256 p0Per1) = _getPriceV3(pool);
            return borrowTokenSmaller ? p1Per0 : p0Per1;
        } else {
            (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool).getReserves();
            return borrowTokenSmaller
                ? (uint256(r1) << 96) / uint256(r0)
                : (uint256(r0) << 96) / uint256(r1);
        }
    }

    function _getPriceV3(address pool)
        private view
        returns (uint160 sqrtPriceX96, uint256 price1Per0Q96, uint256 price0Per1Q96)
    {
        (sqrtPriceX96,,,,,,) = IUniswapV3Pool(pool).slot0();
        uint256 priceX192 = uint256(sqrtPriceX96) * uint256(sqrtPriceX96);
        price1Per0Q96     = priceX192 >> 96;
        price0Per1Q96     = price1Per0Q96 > 0 ? (uint256(1) << 192) / price1Per0Q96 : 0;
    }

    // -------------------------------------------------------------------------
    // Optimal borrow calculation — unified for V2/V2, V3/V3, V2/V3
    // -------------------------------------------------------------------------

    /// @dev Computes the profit-maximising borrow amount for a 2-pool arb.
    ///
    ///      Works for all pool type combinations (V2/V2, V3/V3, V2/V3):
    ///        - V2 pools  → real reserves from getReserves()
    ///        - V3 pools  → effective virtual reserves (L/√P, L·√P) from slot0+liquidity
    ///
    ///      The approximation is exact for V2 and accurate within the current tick
    ///      for V3. If the optimal amount would cross a tick boundary, the off-chain
    ///      bot should override amountIn via the golden-section + Quoter approach
    ///      before calling execute().
    ///
    ///      Caller must pass reserves in trade direction:
    ///        resInP0  — reserve of tokenIn  in the borrow pool  (pools[0])
    ///        resOutP0 — reserve of tokenOut in the borrow pool  (pools[0])
    ///        resInP1  — reserve of tokenIn  in the unwind pool  (pools[1])  ← intermediate token
    ///        resOutP1 — reserve of tokenOut in the unwind pool  (pools[1])  ← back to tokenIn
    ///
    ///      mode 0: borrow tokenIn, repay tokenIn (standard flash loan)
    ///      mode 1: borrow intermediate, repay intermediate (flash swap)
    function calcOptimalV2Borrow(
        uint256 resInP0,
        uint256 resOutP0,
        uint256 resInP1,
        uint256 resOutP1,
        uint24  feeP0,
        uint24  feeP1,
        uint8   mode
    ) internal pure returns (uint256 amount) {
        // Scale down to avoid overflow in quadratic (int256 safe math)
        uint256 min1 = resInP0 < resOutP0 ? resInP0 : resOutP0;
        uint256 min2 = resInP1 < resOutP1 ? resInP1 : resOutP1;
        uint256 min = min1 < min2 ? min1 : min2;
        uint256 d = _scalingFactor(min);
        
        int256 a1 = int256(resInP0 / d); 
        int256 b1 = int256(resOutP0 / d); 
        int256 a2 = int256(resInP1 / d);  
        int256 b2 = int256(resOutP1 / d); 

        // gamma_i = (1e6 - fee_i), representing (1 - fee) scaled to 1e6
        int256 g0 = int256(uint256(1e6 - feeP0));
        int256 g1 = int256(uint256(1e6 - feeP1));

        // Profit(x) = getAmountOut(getAmountOut(x, P0), P1) - x
        // dP/dx = 0  →  quadratic in x
        int256 k  = (a2 * g1) / 1e6 + (b1 * g0 * g1) / 1e12;
        int256 qa = k * k;
        int256 qb = 2 * k * a1 * a2;
        int256 qc = a1 * a2 * a1 * a2 - (b1 * a1 * a2 * b2 * g0 * g1) / 1e12;

        (int256 x1, int256 x2) = _solveQuadratic(qa, qb, qc);

        // Pick the positive root that lies within available liquidity
        int256 x = (x1 > 0 && x1 < b2) ? x1 : x2;
        if (x <= 0 || x >= b2) return 0;

        amount = uint256(x) * d;

        // Mode 1: caller needs the intermediate token amount, not tokenIn amount
        if (mode == 1) amount = getAmountOutV2WithFee(amount, resInP0, resOutP0, feeP0);
    }

    /// @dev Unified entry point called by _determineBorrowAmount in ArbExec.
    ///      Resolves reserves for both pools (handling V2/V2, V3/V3, V2/V3 transparently)
    ///      and delegates to calcOptimalV2Borrow.
    ///
    ///      Requires pools to already be sorted (pools[0] = borrow, pools[1] = unwind)
    ///      and tokens[0]/tokens[1] to reflect the correct trade direction.
    function calcOptimalBorrow(
        address[] memory pools,
        address[] memory tokens,
        uint24[]  memory fees,
        uint8 mode
    ) internal view returns (uint256) {
        // pools[0]: sell tokens[0] (tokenIn), receive tokens[1] (intermediate)
        // pools[1]: sell tokens[1] (intermediate), receive tokens[0] (tokenIn)
        (uint256 resInP0,  uint256 resOutP0)  = _getOrderedReserves(pools[0], tokens[0]);
        (uint256 resInP1,  uint256 resOutP1)  = _getOrderedReserves(pools[1], tokens[1]);
        return calcOptimalV2Borrow(resInP0, resOutP0, resInP1, resOutP1, fees[0], fees[1], mode);
    }

    // -------------------------------------------------------------------------
    // Quadratic solver & scaling
    // -------------------------------------------------------------------------

    function _solveQuadratic(int256 a, int256 b, int256 c)
        private pure
        returns (int256 x1, int256 x2)
    {
        int256 disc = b * b - 4 * a * c;
        if (disc <= 0) return (0, 0);
        int256 sqrtDisc = int256(sqrt(uint256(disc)));
        x1 = (-b + sqrtDisc) / (2 * a);
        x2 = (-b - sqrtDisc) / (2 * a);
    }

    /// @dev Integer square root via Newton's method.
    function sqrt(uint256 n) internal pure returns (uint256 res) {
        assert(n > 1);
        uint256 _n = n * 10**6;
        uint256 c  = _n;
        res = _n;
        uint256 xi;
        while (true) {
            xi = (res + c / res) / 2;
            if (res - xi < 1000) break;
            res = xi;
        }
        res = res / 10**3;
    }

    function _scalingFactor(uint256 min) private pure returns (uint256 d) {
        if      (min > 1e24) d = 1e20;
        else if (min > 1e23) d = 1e19;
        else if (min > 1e22) d = 1e18;
        else if (min > 1e21) d = 1e17;
        else if (min > 1e20) d = 1e16;
        else if (min > 1e19) d = 1e15;
        else if (min > 1e18) d = 1e14;
        else if (min > 1e17) d = 1e13;
        else if (min > 1e16) d = 1e12;
        else if (min > 1e15) d = 1e11;
        else                 d = 1e10;
    }

    // -------------------------------------------------------------------------
    // Validation
    // -------------------------------------------------------------------------

    function _validatePoolTokens(address[] memory tokens, address[] memory pools)
        internal view
    {
        for (uint256 i = 0; i < pools.length; i++) {
            require(_isContract(pools[i]), "not contract");
            address tokenIn  = tokens[i];
            address tokenOut = tokens[i + 1];
            (address pt0, address pt1,) = getPoolTokens(pools[i]);
            require(
                (pt0 == tokenIn && pt1 == tokenOut) ||
                (pt0 == tokenOut && pt1 == tokenIn),
                "pool/token mismatch"
            );
        }
    }

    // -------------------------------------------------------------------------
    // Misc
    // -------------------------------------------------------------------------

    function uint2str(uint256 _i) internal pure returns (string memory) {
        if (_i == 0) return "0";
        uint256 j = _i;
        uint256 length;
        while (j != 0) { length++; j /= 10; }
        bytes memory bstr = new bytes(length);
        j = _i;
        while (j != 0) {
            bstr[--length] = bytes1(uint8(48) + uint8(j % 10));
            j /= 10;
        }
        return string(bstr);
    }
}
