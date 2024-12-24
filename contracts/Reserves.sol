// SPDX-License-Identifier: Unlicense
pragma solidity <=0.8.20;
pragma abicoder v2;

import '@openzeppelin/contracts/token/ERC20/IERC20.sol';
import '@uniswap/v3-core/contracts/interfaces/IUniswapV3Pool.sol';
import '@openzeppelin/contracts/access/Ownable.sol';


contract Reserves is Ownable{
    address immutable WETH;

    constructor(address _WETH) Ownable(msg.sender) {
        WETH = _WETH;  
    }

    receive() external payable {
        // You can add any logic that should be executed when Ether is sent directly to this contract.
        revert("Not implemented yet.");
    }

    function reserve0(address pair) external view returns ( uint256 reserve) {
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token0 = pool.token0();
        reserve = IERC20(token0).balanceOf(pair);
    }
    
    function reserve01(address pair) external view returns ( uint256 reserve) {
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token1 = pool.token1();
        reserve = IERC20(token1).balanceOf(pair);
    }
}