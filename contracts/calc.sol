// SPDX-License-Identifier: MIT
pragma solidity <= 0.8.20;

import '@uniswap/v3-core/contracts/interfaces/callback/IUniswapV3FlashCallback.sol';
import '@uniswap/v3-core/contracts/libraries/LowGasSafeMath.sol';
import '@uniswap/v3-periphery/contracts/libraries/PoolAddress.sol';
import '@uniswap/v3-periphery/contracts/base/PeripheryImmutableState.sol';
import '@uniswap/v3-periphery/contracts/libraries/CallbackValidation.sol';
import '@uniswap/v3-periphery/contracts/libraries/TransferHelper.sol';
import '@uniswap/v3-periphery/contracts/interfaces/ISwapRouter.sol';
import '@uniswap/v3-periphery/contracts/base/PeripheryPayments.sol';



contract ArbitrageCalculator {
    function getLiquidityAndPrice(address poolAddress) public view returns (uint256 _liquidity, uint256 _priceX96)
    {
        IUniswapV3Pool pool = IUniswapV3Pool(poolAddress);
        (_priceX96,,,,,,) = pool.slot0();
        _liquidity = pool.liquidity();
        
    }

    function getMaxProfitableAmount(address lowPoolAddress, address highPoolAddress) public view returns (uint256 _mpa)
    {
        // Get relative values between pools
        uint256 relLiquidity = getRelativeLiquidity(lowPoolAddress, highPoolAddress);
        uint256 relPriceQuoteLowHigh = getPriceRatio(highPoolAddress, lowPoolAddress);

        return (relLiquidity * relPriceQuoteLowHigh) / (1e18); 
    }

    function getRelativeLiquidity(address poolA, address poolB) public view returns (uint256 _rel)
    {
        (uint256 liquidityPoolA,) = getLiquidityAndPrice(poolA);
        (uint256 liquidityPoolB,) = getLiquidityAndPrice(poolB);

        return (liquidityPoolA / 1e18 * 1000000 - liquidityPoolB) / (liquidityPoolB + liquidityPoolA/2); 
    }

    function getPriceRatio(address poolHigh, address poolLow) public view returns (uint256 rel)
    {
        (,uint256 highQuote) = getLiquidityAndPrice(poolHigh);
        (,uint256 lowQuote) = getLiquidityAndPrice(poolLow);

        rel = (highQuote / 1e18 * 1000000 - lowQuote )/(lowQuote +highQuote)/2; 
    }
}