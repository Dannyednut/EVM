// SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.0;
pragma abicoder v2;

import '@openzeppelin/contracts/token/ERC20/IERC20.sol';
import '@uniswap/v3-core/contracts/interfaces/IUniswapV3Pool.sol';
import '@openzeppelin/contracts/access/Ownable.sol';

import './interfaces/IUniswapV2Pair.sol';

contract Reserves{


    function reserves0(address pair) external view returns ( uint256 reserve) {
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token0 = pool.token0();
        reserve = IERC20(token0).balanceOf(pair);
    }
    
    function reserves1(address pair) external view returns ( uint256 reserve) {
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token1 = pool.token1();
        reserve = IERC20(token1).balanceOf(pair);
    }

    function getReservesV3(address pair) public view returns (uint256 reserve0, uint256 reserve1){
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token0 = pool.token0();
        address token1 = pool.token1();
        reserve0 = IERC20(token0).balanceOf(pair);
        reserve1 = IERC20(token1).balanceOf(pair);
    }

    function getReservesV2(address pair) public view returns (uint256 reserve0, uint256 reserve1){
        IUniswapV2Pair pool = IUniswapV2Pair(pair);
        address token0 = pool.token0();
        address token1 = pool.token1();
        reserve0 = IERC20(token0).balanceOf(pair);
        reserve1 = IERC20(token1).balanceOf(pair);
    }
}