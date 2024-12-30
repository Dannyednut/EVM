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

        amount = calcBorrowAmount(reserves);
    }

    function getBorrowAmountV3(address lowerPool, address higherPool) external view returns(uint256 amount){
        OrderedReserves memory reserves;

        (reserves.a1, reserves.b1) = getReservesV3(lowerPool);
        (reserves.a2, reserves.b2) = getReservesV3(higherPool);

        amount = calcBorrowAmount(reserves);
    }

    function calcBorrowAmount(OrderedReserves memory reserves) internal pure returns (uint256 amount) {
        // we can't use a1,b1,a2,b2 directly, because it will result overflow/underflow on the intermediate result
        // so we:
        //    1. divide all the numbers by d to prevent from overflow/underflow
        //    2. calculate the result by using above numbers
        //    3. multiply d with the result to get the final result
        // Note: this workaround is only suitable for ERC20 token with 18 decimals, which I believe most tokens do

        uint256 min1 = reserves.a1 < reserves.b1 ? reserves.a1 : reserves.b1;
        uint256 min2 = reserves.a2 < reserves.b2 ? reserves.a2 : reserves.b2;
        uint256 min = min1 < min2 ? min1 : min2;

        // choose appropriate number to divide based on the minimum number
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

        int256 a = a1 * b1 - a2 * b2;
        int256 b = 2 * b1 * b2 * (a1 + a2);
        int256 c = b1 * b2 * (a1 * b2 - a2 * b1);

        (int256 x1, int256 x2) = calcSolutionForQuadratic(a, b, c);

        // 0 < x < b1 and 0 < x < b2
        require((x1 > 0 && x1 < b1 && x1 < b2) || (x2 > 0 && x2 < b1 && x2 < b2), 'Wrong input order');
        amount = (x1 > 0 && x1 < b1 && x1 < b2) ? uint256(x1) * d : uint256(x2) * d;
    }

    /// @dev find solution of quadratic equation: ax^2 + bx + c = 0, only return the positive solution
    function calcSolutionForQuadratic(
        int256 a,
        int256 b,
        int256 c
    ) internal pure returns (int256 x1, int256 x2) {
        int256 m = b**2 - 4 * a * c;
        // m < 0 leads to complex number
        require(m > 0, 'Complex number');

        int256 sqrtM = int256(sqrt(uint256(m)));
        x1 = (-b + sqrtM) / (2 * a);
        x2 = (-b - sqrtM) / (2 * a);
    }

    /// @dev Newton’s method for caculating square root of n
    function sqrt(uint256 n) internal pure returns (uint256 res) {
        assert(n > 1);

        // The scale factor is a crude way to turn everything into integer calcs.
        // Actually do (n * 10 ^ 4) ^ (1/2)
        uint256 _n = n * 10**6;
        uint256 c = _n;
        res = _n;

        uint256 xi;
        while (true) {
            xi = (res + c / res) / 2;
            // don't need be too precise to save gas
            if (res - xi < 1000) {
                break;
            }
            res = xi;
        }
        res = res / 10**3;
    }

}