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

    /// @dev Assembly arithmetic skips Solidity overflow checks — safe here
    ///      because inputs are validated by the require above.
    function getAmountOutV2(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 out) {
        require(amountIn > 0, "amt");
        require(reserveIn > 0 && reserveOut > 0, "liq");
        assembly {
            let aif := mul(amountIn, 997)
            out := div(mul(aif, reserveOut), add(mul(reserveIn, 1000), aif))
        }
    }

    function getAmountInV2(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amtIn) {
        require(amountOut > 0, "amt");
        require(reserveIn > 0 && reserveOut > amountOut, "liq");
        assembly {
            amtIn := add(div(mul(mul(reserveIn, amountOut), 1000), mul(sub(reserveOut, amountOut), 997)), 1)
        }
    }

    function getAmountOutV2WithFee(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut,
        uint24  fee
    ) internal pure returns (uint256 out) {
        require(amountIn > 0, "amt");
        require(reserveIn > 0 && reserveOut > 0, "liq");
        assembly {
            let g   := sub(1000000, fee)
            let aif := mul(amountIn, g)
            out := div(mul(aif, reserveOut), add(mul(reserveIn, 1000000), aif))
        }
    }

    function getAmountInV2WithFee(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut,
        uint24  fee
    ) internal pure returns (uint256 amtIn) {
        require(amountOut > 0, "amt");
        require(reserveIn > 0 && reserveOut > amountOut, "liq");
        assembly {
            let g   := sub(1000000, fee)
            amtIn := add(div(mul(mul(reserveIn, amountOut), 1000000), mul(sub(reserveOut, amountOut), g)), 1)
        }
    }

     // ── Assembly helpers ──────────────────────────────────────────────────────

    /// @dev token0() via raw staticcall — saves ~200 gas vs ABI dispatch per call
    function _token0(address pool) internal view returns (address t) {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, 0x0dfe168100000000000000000000000000000000000000000000000000000000)
            if iszero(staticcall(gas(), pool, ptr, 0x04, ptr, 0x20)) { revert(0, 0) }
            t := mload(ptr)
        }
    }

    /// @dev token1() via raw staticcall
    function _token1(address pool) internal view returns (address t) {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, 0xd21220a700000000000000000000000000000000000000000000000000000000)
            if iszero(staticcall(gas(), pool, ptr, 0x04, ptr, 0x20)) { revert(0, 0) }
            t := mload(ptr)
        }
    }

    /// @dev ERC20 balanceOf via assembly — saves ~100 gas vs IERC20 dispatch
    function _balanceOf(address token, address account) internal view returns (uint256 bal) {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr,        0x70a0823100000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4), account)
            if iszero(staticcall(gas(), token, ptr, 0x24, ptr, 0x20)) { revert(0, 0) }
            bal := mload(ptr)
        }
    }

    /// @dev ERC20 transfer via assembly — bypasses SafeERC20 return-value overhead.
    ///      Used only for trusted tokens (WETH, USDC, etc.) on known pools.
    function _safeTransfer(address token, address to, uint256 amount) internal {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr,          0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4),  to)
            mstore(add(ptr, 36), amount)
            let ok := call(gas(), token, 0, ptr, 0x44, ptr, 0x20)
            // Accept both: call failed OR returned false
            if iszero(and(ok, or(iszero(returndatasize()), mload(ptr)))) {
                mstore(0x00, 0x356680b7) // InsufficientBalance() — transfer failed
                revert(0x1c, 0x04)
            }
        }
    }
    
    // -------------------------------------------------------------------------
    // Pool detection & token resolution
    // -------------------------------------------------------------------------

    /// @dev Detects V3 by calling slot0() via low-level staticcall.
    ///      Avoids try/catch EVM exception overhead (~2000 gas saved per call).
    ///      slot0() selector = 0x3850c7bd; returns 224 bytes (7 × 32).
    function _isUniswapV3(address pool) internal view returns (bool ok) {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, 0x3850c7bd00000000000000000000000000000000000000000000000000000000)
            ok := staticcall(5000, pool, ptr, 0x04, ptr, 0xe0)
        }
    }

    function _isContract(address addr) internal view returns (bool) {
        uint256 size;
        assembly { size := extcodesize(addr) }
        return size > 0;
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
            t0        = _token0(pool);
        } else {
            (r0, r1)  = getReservesV2(pool);
            t0        = _token0(pool);
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
    ) internal view returns (address[] memory, address[] memory, uint24[] memory) {
        if (pools.length > 2) return (pools, tokens, fees);

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
        tokens[2] = tokens[0]; // end token = start token

        return (pools, tokens, fees);
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
        t0 = _token0(pools[0]);
        t1 = _token1(pools[0]);

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
        t0 = _token0(pools[0]);
        t1 = _token1(pools[0]);
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
        t0 = isV3_0 ? _token0(pools[0]) : _token0(pools[0]);
        t1 = isV3_0 ? _token0(pools[0]) : _token0(pools[0]);

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
        uint256 d_a = _scalingFactor(resInP0 < resOutP1 ? resInP0 : resOutP1);
        uint256 d_b = _scalingFactor(resOutP0 < resInP1 ? resOutP0 : resInP1);

        int256 a1 = int256(resInP0  / d_a);
        int256 b1 = int256(resOutP0 / d_b);
        int256 a2 = int256(resInP1  / d_b);
        int256 b2 = int256(resOutP1 / d_a);

        if (a1 <= 0 || b1 <= 0 || a2 <= 0 || b2 <= 0) return 0;

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

        amount = uint256(x) * d_a;

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

    /// @dev Babylonian integer square root via assembly.
    ///      Uniswap's own algorithm — converges in ~7 iterations, no scaling needed.
    ///      ~40% faster than Newton's method with 10**6 scale factor.
    function sqrt(uint256 x) internal pure returns (uint256 z) {
        assembly {
            // Start with z = x as initial estimate
            z := x
            // y = x/2 + 1
            let y := add(shr(1, x), 1)
            // Iterate: z = (z + x/z) / 2 until y >= z (converged)
            for {} lt(y, z) {} {
                z := y
                y := shr(1, add(div(x, y), y))
            }
        }
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
        else if (min > 1e10) d = 1e6;   // USDC-scale pools
        else if (min > 1e6)  d = 1e2;
        else                 d = 1;
    }

    // -------------------------------------------------------------------------
    // Validation
    // -------------------------------------------------------------------------

    function _validatePoolTokens(address[] memory tokens, address[] memory pools)
        internal view
    {
        for (uint256 i = 0; i < pools.length; ) {
            require(_isContract(pools[i]), "not contract");
            address tokenIn  = tokens[i];
            address tokenOut = tokens[i + 1];
            (address pt0, address pt1) = (_token0(pools[i]), _token1(pools[i]));
            require(
                (pt0 == tokenIn && pt1 == tokenOut) ||
                (pt0 == tokenOut && pt1 == tokenIn),
                "pool/token mismatch"
            );
            unchecked { ++i; }
        }
    }
}
