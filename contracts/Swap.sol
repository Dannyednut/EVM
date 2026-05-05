// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "./interfaces/IUniswapV2Pair.sol";
import "./interfaces/IUniswapV3Pool.sol";
import "./interfaces/IWETH.sol";

error ZeroAmount();
error ZeroAddress();
error SlippageExceeded(uint256 got, uint256 min);
error TransferFailed();
error InvalidPool();

/// @title  DirectSwap
/// @notice Pull tokenIn (ETH or ERC20) from msg.sender and execute a single
///         hop swap through a Uniswap V2 pair or V3 pool, delivering tokenOut
///         to the specified recipient.
///
///         ETH callers:   send ETH via swapETH() — no approval needed.
///                        ETH is wrapped to WETH internally before swapping.
///         ERC20 callers: approve this contract for at least amountIn,
///                        then call swap().
contract DirectSwap {

    address public immutable WETH;

    /// @dev Set transiently around V3 swap calls to authenticate the callback.
    address private _expectedV3Pool;

    event Swapped(
        address indexed pool,
        address indexed tokenIn,
        address indexed tokenOut,
        uint256 amountIn,
        uint256 amountOut,
        address to
    );

    constructor(address _weth) {
        if (_weth == address(0)) revert ZeroAddress();
        WETH = _weth;
    }

    /// @dev Accepts ETH from WETH.withdraw() and swapETH callers.
    receive() external payable {}

    // ── Entry points ───────────────────────────────────────────────────────

    /// @notice Swap ERC20 → ERC20 (or WETH) through a single V2/V3 pool.
    /// @param pool         V2 pair or V3 pool address.
    /// @param tokenIn      Token to sell. Caller must have approved this contract.
    /// @param tokenOut     Token to receive.
    /// @param amountIn     Exact amount of tokenIn to pull from caller.
    /// @param minAmountOut Minimum tokenOut to accept (slippage guard). 0 = no guard.
    /// @param to           Recipient of tokenOut.
    /// @return amountOut   Actual tokenOut delivered to `to`.
    function swap(
        address pool,
        address tokenIn,
        address tokenOut,
        uint256 amountIn,
        uint256 minAmountOut,
        address to
    ) external returns (uint256 amountOut) {
        if (amountIn == 0)       revert ZeroAmount();
        if (to == address(0))    revert ZeroAddress();
        if (pool == address(0))  revert ZeroAddress();

        // Pull tokenIn from caller into this contract
        _pullFrom(tokenIn, msg.sender, amountIn);

        amountOut = _route(pool, tokenIn, amountIn, to);

        if (minAmountOut > 0 && amountOut < minAmountOut)
            revert SlippageExceeded(amountOut, minAmountOut);

        emit Swapped(pool, tokenIn, tokenOut, amountIn, amountOut, to);
    }

    /// @notice Swap native ETH → ERC20 through a single V2/V3 pool.
    ///         Pool must contain WETH. ETH is wrapped automatically.
    /// @param pool         V2 pair or V3 pool address containing WETH.
    /// @param tokenOut     Token to receive.
    /// @param minAmountOut Minimum tokenOut to accept (slippage guard). 0 = no guard.
    /// @param to           Recipient of tokenOut.
    /// @return amountOut   Actual tokenOut delivered to `to`.
    function swapETH(
        address pool,
        address tokenOut,
        uint256 minAmountOut,
        address to
    ) external payable returns (uint256 amountOut) {
        if (msg.value == 0)      revert ZeroAmount();
        if (to == address(0))    revert ZeroAddress();
        if (pool == address(0))  revert ZeroAddress();

        // Wrap ETH → WETH held by this contract
        IWETH(WETH).deposit{value: msg.value}();

        amountOut = _route(pool, WETH, msg.value, to);

        if (minAmountOut > 0 && amountOut < minAmountOut)
            revert SlippageExceeded(amountOut, minAmountOut);

        emit Swapped(pool, WETH, tokenOut, msg.value, amountOut, to);
    }

    // ── Internal routing ───────────────────────────────────────────────────

    /// @dev Detect pool version and dispatch to the correct swap implementation.
    function _route(
        address pool,
        address tokenIn,
        uint256 amountIn,
        address to
    ) internal returns (uint256 out) {
        return _isV3(pool)
            ? _swapV3(pool, tokenIn, amountIn, to)
            : _swapV2(pool, tokenIn, amountIn, to);
    }

    // ── V2 swap ────────────────────────────────────────────────────────────

    /// @dev Push tokenIn to the V2 pair then call swap() to pull tokenOut.
    ///      V2 protocol: you transfer tokenIn first, then the pair verifies
    ///      its balance increased before releasing tokenOut. No callback needed.
    function _swapV2(
        address pool,
        address tokenIn,
        uint256 amountIn,
        address to
    ) internal returns (uint256 out) {
        address t0 = _token0(pool);
        bool zeroForOne = tokenIn == t0;

        (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool).getReserves();
        (uint256 rIn, uint256 rOut) = zeroForOne
            ? (uint256(r0), uint256(r1))
            : (uint256(r1), uint256(r0));

        out = _getAmountOutV2(amountIn, rIn, rOut);
        if (out == 0) revert ZeroAmount();

        // 1. Push tokenIn to pair
        _transferTo(tokenIn, pool, amountIn);

        // 2. Trigger pair to send tokenOut directly to recipient
        (uint256 out0, uint256 out1) = zeroForOne
            ? (uint256(0), out)
            : (out, uint256(0));

        IUniswapV2Pair(pool).swap(out0, out1, to, "");
    }

    // ── V3 swap ────────────────────────────────────────────────────────────

    /// @dev Initiate a V3 exact-input swap. The pool calls back into
    ///      uniswapV3SwapCallback() to collect tokenIn payment.
    function _swapV3(
        address pool,
        address tokenIn,
        uint256 amountIn,
        address to
    ) internal returns (uint256 out) {
        bool zeroForOne = tokenIn == _token0(pool);

        // Boundary prices — effectively no price limit
        uint160 sqrtLimit = zeroForOne
            ? 4295128740
            : 1461446703485210103287273052203988822378723970341;

        // Authenticate the upcoming callback
        _expectedV3Pool = pool;

        (int256 a0, int256 a1) = IUniswapV3Pool(pool).swap(
            to,                     // tokenOut recipient
            zeroForOne,
            int256(amountIn),       // positive = exact input
            sqrtLimit,
            abi.encode(tokenIn)     // passed through to callback
        );

        _expectedV3Pool = address(0);

        // The pool sends tokenOut to `to` (negative delta = outflow from pool)
        out = zeroForOne ? uint256(-a1) : uint256(-a0);
    }

    /// @notice Uniswap V3 swap callback — called by the pool to collect tokenIn.
    /// @dev    The pool calls this after sending tokenOut to the recipient.
    ///         We owe the pool the positive delta (tokenIn side).
    function uniswapV3SwapCallback(
        int256 amount0Delta,
        int256 amount1Delta,
        bytes calldata data
    ) external {
        if (msg.sender != _expectedV3Pool) revert InvalidPool();

        address tokenIn = abi.decode(data, (address));

        // Positive delta = tokens owed TO the pool
        uint256 owed = amount0Delta > 0
            ? uint256(amount0Delta)
            : uint256(amount1Delta);

        _transferTo(tokenIn, msg.sender, owed);
    }

    // ── Assembly helpers ───────────────────────────────────────────────────

    /// @dev transferFrom(from, address(this), amount) — pulls ERC20 from caller.
    function _pullFrom(address token, address from, uint256 amount) internal {
        assembly {
            let ptr := mload(0x40)
            // transferFrom(address,address,uint256) = 0x23b872dd
            mstore(ptr,          0x23b872dd00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4),  from)
            mstore(add(ptr, 36), address())
            mstore(add(ptr, 68), amount)
            let ok := call(gas(), token, 0, ptr, 0x64, ptr, 0x20)
            if iszero(and(ok, or(iszero(returndatasize()), mload(ptr)))) {
                mstore(0x00, 0x90b8ec18) // TransferFailed()
                revert(0x1c, 0x04)
            }
        }
    }

    /// @dev transfer(to, amount) — sends ERC20 from this contract.
    function _transferTo(address token, address to, uint256 amount) internal {
        assembly {
            let ptr := mload(0x40)
            // transfer(address,uint256) = 0xa9059cbb
            mstore(ptr,          0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4),  to)
            mstore(add(ptr, 36), amount)
            let ok := call(gas(), token, 0, ptr, 0x44, ptr, 0x20)
            if iszero(and(ok, or(iszero(returndatasize()), mload(ptr)))) {
                mstore(0x00, 0x90b8ec18) // TransferFailed()
                revert(0x1c, 0x04)
            }
        }
    }

    /// @dev token0() via raw staticcall — avoids ABI dispatch overhead.
    function _token0(address pool) internal view returns (address t) {
        assembly {
            let ptr := mload(0x40)
            // token0() = 0x0dfe1681
            mstore(ptr, 0x0dfe168100000000000000000000000000000000000000000000000000000000)
            if iszero(staticcall(gas(), pool, ptr, 0x04, ptr, 0x20)) { revert(0, 0) }
            t := mload(ptr)
        }
    }

    /// @dev Detect V3 by probing slot0() — V2 pairs don't have this function.
    ///      Uses a capped gas stipend (5000) to avoid hanging on non-contracts.
    function _isV3(address pool) internal view returns (bool ok) {
        assembly {
            let ptr := mload(0x40)
            // slot0() = 0x3850c7bd
            mstore(ptr, 0x3850c7bd00000000000000000000000000000000000000000000000000000000)
            ok := staticcall(5000, pool, ptr, 0x04, ptr, 0xe0)
        }
    }

    /// @dev Standard V2 constant-product output formula with 0.3% fee.
    ///      amountOut = amountIn * 997 * rOut / (rIn * 1000 + amountIn * 997)
    function _getAmountOutV2(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 out) {
        assembly {
            let aif := mul(amountIn, 997)
            out := div(
                mul(aif, reserveOut),
                add(mul(reserveIn, 1000), aif)
            )
        }
    }
}
