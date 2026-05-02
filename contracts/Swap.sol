// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IERC20 {
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
}

interface IUniswapV2Pair {
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
}

contract DirectV2Swapper {
    
    /**
     * @dev Swaps tokens directly via the pair contract, bypassing the router.
     * @param pair The address of the Uniswap V2 pair (pool).
     * @param tokenIn The address of the token you are swapping.
     * @param amountIn The exact amount of tokenIn to swap.
     * @param amountOutMin The minimum acceptable amount of the output token.
     * @param to The address to receive the output tokens.
     */
    function swapDirect(
        address pair,
        address tokenIn,
        uint256 amountIn,
        uint256 amountOutMin,
        address to
    ) external {
        IUniswapV2Pair pool = IUniswapV2Pair(pair);

        // 1. Identify token0 and token1 from the pair
        address token0 = pool.token0();
        address token1 = pool.token1();
        require(tokenIn == token0 || tokenIn == token1, "Invalid token for this pair");

        // 2. Fetch the current reserves
        (uint112 reserve0, uint112 reserve1, ) = pool.getReserves();

        // 3. Determine which token is 'in' and which is 'out' to assign reserves correctly
        (uint112 reserveIn, uint112 reserveOut) = tokenIn == token0 
            ? (reserve0, reserve1) 
            : (reserve1, reserve0);

        // 4. Calculate the output amount manually using the constant product formula (x * y = k)
        // Uniswap V2 charges a 0.3% fee, so we multiply the input by 997.
        uint256 amountInWithFee = amountIn * 997;
        uint256 numerator = amountInWithFee * reserveOut;
        uint256 denominator = (reserveIn * 1000) + amountInWithFee;
        uint256 amountOut = numerator / denominator;

        // 5. Enforce slippage protection
        require(amountOut >= amountOutMin, "Insufficient output amount");

        // 6. Map the calculated output to the correct token0/token1 parameter
        (uint256 amount0Out, uint256 amount1Out) = tokenIn == token0 
            ? (uint256(0), amountOut) 
            : (amountOut, uint256(0));

        // 7. Optimistic Transfer: Send the input tokens DIRECTLY to the pair contract.
        // The sender must have approved this contract to spend `amountIn`.
        require(
            IERC20(tokenIn).transferFrom(msg.sender, pair, amountIn),
            "Transfer to pair failed"
        );

        // 8. Execute the swap.
        // The pair contract calculates its new balance, compares it to its reserves, 
        // verifies the k-invariant holds, and sends the output tokens to the `to` address.
        // The trailing empty bytes array signals that this is a standard swap, not a flash swap.
        pool.swap(amount0Out, amount1Out, to, new bytes(0));
    }
}