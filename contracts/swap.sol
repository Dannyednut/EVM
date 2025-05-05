// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.20;
pragma abicoder v2;

import '@openzeppelin/contracts/token/ERC20/SafeERC20.sol';
import './interfaces/IUniswapV2Pair.sol';
import './interfaces/IWETH.sol';
import './Reserves.sol';


contract Swap {
    using SafeERC20 for IERC20;

    function swap(address swap_pool, address token_in, uint256 amount_in) external {
       IUniswapV2Pair pool = IUniswapV2Pair(swap_pool);
       address token0 = pool.token0();
       address token1 = pool.token1();
       (uint256 a, uint256 b) = getReservesV2(swap_pool);
       require((token_in == token0) || (token_in == token1), 'No token in pair');
       bool isbaseToken = token_in == token0 ? true : false;

       IERC20(token_in).safeTransfer(swap_pool, amount_in);

       (uint256 amount0Out, uint256 amount1Out) =
            isbaseToken ? (uint256(0), getAmountOut(amount_in, a, b)) : (getAmountOut(amount_in, b, a), uint256(0));

        IUniswapV2Pair(swap_pool).swap(amount0Out, amount1Out, address(this), new bytes(0));

    }

    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountIn) {
        require(amountOut > 0, 'UniswapV2Library: INSUFFICIENT_OUTPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
        uint256 numerator = reserveIn * amountOut * 1000; // Replace .mul() with *
        uint256 denominator = (reserveOut - amountOut) * 997; // Replace .sub() with -
        amountIn = (numerator / denominator) + 1;
    }

    // copy from UniswapV2Library
    // given an input amount of an asset and pair reserves, returns the maximum output amount of the other asset
    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountOut) {
        require(amountIn > 0, 'UniswapV2Library: INSUFFICIENT_INPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV2Library: INSUFFICIENT_LIQUIDITY');
        uint256 amountInWithFee = amountIn * 997; // Replace .mul() with *
        uint256 numerator = amountInWithFee * reserveOut; // Replace .mul() with *
        uint256 denominator = reserveIn * 1000 + amountInWithFee; // Replace .add() with +
        amountOut = numerator / denominator;
    }

    function getReservesV2(address pair) public view returns (uint256 reserve0, uint256 reserve1){
        IUniswapV2Pair pool = IUniswapV2Pair(pair);
        address token0 = pool.token0();
        address token1 = pool.token1();
        reserve0 = IERC20(token0).balanceOf(pair);
        reserve1 = IERC20(token1).balanceOf(pair);
    }
}