// SPDX-License-Identifier: MIT
pragma solidity ^ 0.8.0;

import '@uniswap/v3-core/contracts/interfaces/IUniswapV3Pool.sol';

import './libraries/Math.sol';
import './Reserves.sol';

struct OrderedReserves {
    uint256 a1; // base asset
    uint256 b1;
    uint256 a2;
    uint256 b2;
}

contract ArbitrageCalculator is Reserves {
    using MyMathLibrary for uint256;

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

    
    function getBorrowAmountV2(address lowerPool, address higherPool) external view returns(uint256 amount){
        OrderedReserves memory reserves;

        (reserves.a1, reserves.b1) = getReservesV2(lowerPool);
        (reserves.a2, reserves.b2) = getReservesV2(higherPool);

        amount = calcMaxBorrowableAmount(reserves);
    }

    function getBorrowAmountV3(address lowerPool, address higherPool) external view returns(uint256 amount){
        OrderedReserves memory reserves;

        (reserves.a1, reserves.b1) = getReservesV3(lowerPool);
        (reserves.a2, reserves.b2) = getReservesV3(higherPool);

        amount = calcMaxBorrowableAmount(reserves);
    }

    function calcMaxBorrowableAmount(OrderedReserves memory reserves) internal pure returns (uint256 amount) {
        // Choose a smaller reserve as the base for calculation, considering which pool has more liquidity in its respective asset.
        
        int256 min = MyMathLibrary.min(int256(reserves.a1 * reserves.b2), int256(reserves.b1 * reserves.a2));

        if(min <= 0){
            return 0;
        }

        uint256 d;
        if (min > 1e24) {
            d = 1e20;
        } else if (min > 1e23) {
            d = 1e19;
        } else if (min > 1e22) {
            d = 1e18;
        } else if (min > 1e21) {
            d = 1e17;
        } else if (min > 1e20) {
            d = 1e16;
        } else if (min > 1e19) {
            d = 1e15;
        } else if (min > 1e18) {
            d = 1e14;
        } else if (min > 1e17) {
            d = 1e13;
        } else if (min > 1e16) {
            d = 1e12;
        } else if (min > 1e15) {
            d = 1e11;
        } else {
            d = 1e10;
        }

        (int256 a1, int256 a2, int256 b1, int256 b2) =
            (int256(reserves.a1 / d), int256(reserves.a2 / d), int256(reserves.b1 / d), int256(reserves.b2 / d)); 
        // Use a different approach based on the pools' reserve ratios to determine borrowable amount
        require(a2 < b2, 'Wrong input order');
        
        int256 max = MyMathLibrary.max(MyMathLibrary.abs((a1 * b2) - (b1 * a2)),MyMathLibrary.abs( ((a1 * b2))));
            
            if(max == 0){
                return 0;
            }
                
        // Calculate the maximum borrowable amount by taking a percentage of `min` based on pool reserve ratios
        int256 borrowableAmount = MyMathLibrary.min(min, (max / max) * min);
        
        require(borrowableAmount > 0,'Wrong input order');
            
    return uint256(borrowableAmount);
    }
}