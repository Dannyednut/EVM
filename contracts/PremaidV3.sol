// SPDX-License-Identifier: GPL-2.0-or-later

pragma solidity ^0.8.0;
pragma abicoder v2;

import '@uniswap/v3-core/contracts/interfaces/callback/IUniswapV3FlashCallback.sol';
import '@uniswap/v3-periphery/contracts/interfaces/ISwapRouter.sol';
import '@uniswap/v3-core/contracts/libraries/LowGasSafeMath.sol';
import '@uniswap/v3-periphery/contracts/base/PeripheryPayments.sol';
import '@uniswap/v3-periphery/contracts/base/PeripheryImmutableState.sol';
import '@uniswap/v3-periphery/contracts/libraries/PoolAddress.sol';
import '@uniswap/v3-periphery/contracts/libraries/CallbackValidation.sol';
import '@uniswap/v3-periphery/contracts/libraries/TransferHelper.sol';
import '@openzeppelin/contracts/utils/EnumerableSet.sol';
import '@openzeppelin/contracts/access/Ownable.sol';
import 'hardhat/console.sol';

import './libraries/Decimal.sol';


struct OrderedReserves {
    uint256 a1; // base asset
    uint256 b1;
    uint256 a2;
    uint256 b2;
    uint24 fee0;
    uint24 fee1;
}

struct ArbitrageInfo {
    address baseToken;
    address quoteToken;
    bool baseTokenSmaller;
    address lowerPool; // pool with lower price, denominated in quote asset
    address higherPool; // pool with higher price, denominated in quote asset
    uint256 borrowedAmount;
    uint256 debtTokenOutAmount;
}

// fee2 and fee3 are the two other fees associated with the two other pools of token0 and token1
    struct FlashCallbackData {
        uint256 amount0;
        uint256 amount1;
        address payer;
        PoolAddress.PoolKey poolKey;
        uint24 poolFee2;
        uint24 poolFee3;
    }

/// @title Flash contract implementation
/// @notice An example contract using the Uniswap V3 flash function
contract PoolFlash is IUniswapV3FlashCallback, Ownable {
    using LowGasSafeMath for uint256;
    using LowGasSafeMath for int256;
    using EnumerableSet for EnumerableSet.AddressSet;
    using Decimal for Decimal.D256;

    // ACCESS CONTROL
    // Only the `permissionedPairAddress` may call the `uniswapV2Call` function
    address permissionedPairAddress = address(1);

    // WETH on ETH or WBNB on BSC
    address immutable WETH9;

    // AVAILABLE BASE TOKENS
    EnumerableSet.AddressSet baseTokens;

    event Withdrawn(address indexed to, uint256 indexed value);
    event BaseTokenAdded(address indexed token);
    event BaseTokenRemoved(address indexed token);

    constructor(address _WETH9) Ownable(msg.sender) {
        WETH9 = _WETH9;
        baseTokens.add(_WETH9);
    }

    // Receive Ether
    receive() external payable {}

    fallback() external {
        // Handle unexpected calls or redirect to a specific function
        // For example, you could log the call or revert
        revert("Fallback function called: Invalid function call");
    }

    function withdraw() external {
        uint256 balance = address(this).balance;
        if (balance > 0) {
            payable(owner()).transfer(balance);
            emit Withdrawn(owner(), balance);
        }

        for (uint256 i = 0; i < baseTokens.length(); i++) {
            address token = baseTokens.at(i);
            balance = IERC20(token).balanceOf(address(this));
            if (balance > 0) {
                // do not use safe transfer here to prevents revert by any shitty token
                IERC20(token).transfer(owner(), balance);
            }
        }
    }

    function addBaseToken(address token) external onlyOwner {
        baseTokens.add(token);
        emit BaseTokenAdded(token);
    }

    function removeBaseToken(address token) external onlyOwner {
        uint256 balance = IERC20(token).balanceOf(address(this));
        if (balance > 0) {
            // do not use safe transfer to prevents revert by any shitty token
            IERC20(token).transfer(owner(), balance);
        }
        baseTokens.remove(token);
        emit BaseTokenRemoved(token);
    }

    function getBaseTokens() external view returns (address[] memory tokens) {
        uint256 length = baseTokens.length();
        tokens = new address[](length);
        for (uint256 i = 0; i < length; i++) {
            tokens[i] = baseTokens.at(i);
        }
    }
    function baseTokensContains(address token) public view returns (bool) {
        return baseTokens.contains(token);
    }

    function isbaseTokenSmaller(address pool0, address pool1)
        internal
        view
        returns (
            bool baseSmaller,
            address baseToken,
            address quoteToken
        )
    {
        require(pool0 != pool1, 'Same pair address');
        (address pool0Token0, address pool0Token1) = (IUniswapV3Pool(pool0).token0(), IUniswapV3Pool(pool0).token1());
        (address pool1Token0, address pool1Token1) = (IUniswapV3Pool(pool1).token0(), IUniswapV3Pool(pool1).token1());
        require(pool0Token0 < pool0Token1 && pool1Token0 < pool1Token1, 'Non standard uniswap AMM pair');
        require(pool0Token0 == pool1Token0 && pool0Token1 == pool1Token1, 'Require same token pair');
        require(baseTokensContains(pool0Token0) || baseTokensContains(pool0Token1), 'No base token in pair');

        (baseSmaller, baseToken, quoteToken) = baseTokensContains(pool0Token0)
            ? (true, pool0Token0, pool0Token1)
            : (false, pool0Token1, pool0Token0);
    }

    function getReserves(address pair) internal view returns (uint256 reserve0, uint256 reserve1){
        IUniswapV3Pool pool = IUniswapV3Pool(pair);
        address token0 = pool.token0();
        address token1 = pool.token1();
        reserve0 = IERC20(token0).balanceOf(pair);
        reserve1 = IERC20(token1).balanceOf(pair);
    }

    /// @param token The token to pay
    /// @param payer The entity that must pay
    /// @param recipient The entity that will receive payment
    /// @param value The amount to pay
    function pay(
        address token,
        address payer,
        address recipient,
        uint256 value
    ) internal {
        if (token == WETH9 && address(this).balance >= value) {
            // pay with WETH9
            IWETH9(WETH9).deposit{value: value}(); // wrap only what is needed to pay
            IWETH9(WETH9).transfer(recipient, value);
        } else if (payer == address(this)) {
            // pay with tokens already in the contract (for the exact input multihop case)
            TransferHelper.safeTransfer(token, recipient, value);
        } else {
            // pull payment
            TransferHelper.safeTransferFrom(token, payer, recipient, value);
        }
    }

    /// @dev Compare price denominated in quote token between two pools
    /// We borrow base token by using flash swap from lower price pool and sell them to higher price pool
    function getOrderedReserves(
        address pool0,
        address pool1,
        bool baseTokenSmaller
    )
        internal
        view
        returns (
            address lowerPool,
            address higherPool,
            OrderedReserves memory orderedReserves
        )
    {
        (uint256 pool0Reserve0, uint256 pool0Reserve1) = getReserves(pool0);
        (uint256 pool1Reserve0, uint256 pool1Reserve1) = getReserves(pool1);

        // Calculate the price denominated in quote asset token
        (Decimal.D256 memory price0, Decimal.D256 memory price1) =
            baseTokenSmaller
                ? (Decimal.from(pool0Reserve0).div(pool0Reserve1), Decimal.from(pool1Reserve0).div(pool1Reserve1))
                : (Decimal.from(pool0Reserve1).div(pool0Reserve0), Decimal.from(pool1Reserve1).div(pool1Reserve0));

        uint24 fee0 = IUniswapV3Pool(pool0).fee();
        uint24 fee1 = IUniswapV3Pool(pool1).fee();

        // get a1, b1, a2, b2 with following rule:
        // 1. (a1, b1) represents the pool with lower price, denominated in quote asset token
        // 2. (a1, a2) are the base tokens in two pools
        if (price0.lessThan(price1)) {
            (lowerPool, higherPool) = (pool0, pool1);
            (orderedReserves.a1, orderedReserves.b1, orderedReserves.a2, orderedReserves.b2) = baseTokenSmaller
                ? (pool0Reserve0, pool0Reserve1, pool1Reserve0, pool1Reserve1)
                : (pool0Reserve1, pool0Reserve0, pool1Reserve1, pool1Reserve0);
            (orderedReserves.fee0, orderedReserves.fee1) = (fee0, fee1);
        } else {
            (lowerPool, higherPool) = (pool1, pool0);
            (orderedReserves.a1, orderedReserves.b1, orderedReserves.a2, orderedReserves.b2) = baseTokenSmaller
                ? (pool1Reserve0, pool1Reserve1, pool0Reserve0, pool0Reserve1)
                : (pool1Reserve1, pool1Reserve0, pool0Reserve1, pool0Reserve0);
            (orderedReserves.fee0, orderedReserves.fee1) = (fee1, fee0);

            
        }
        console.log('Borrow from pool:', lowerPool);
        console.log('Sell to pool:', higherPool);
    }

    /// @notice Do an arbitrage between two Uniswap-like AMM pools
    /// @dev Two pools must contains same token pair
    function flashTrade(address pool0, address pool1) external {
        ArbitrageInfo memory info;
        (info.baseTokenSmaller, info.baseToken, info.quoteToken) = isbaseTokenSmaller(pool0, pool1);

        OrderedReserves memory orderedReserves;
        (info.lowerPool, info.higherPool, orderedReserves) = getOrderedReserves(pool0, pool1, info.baseTokenSmaller);

        // this must be updated every transaction for callback origin authentication
        permissionedPairAddress = info.lowerPool;

        uint256 balanceBefore = IERC20(info.baseToken).balanceOf(address(this));

        // avoid stack too deep error
        {
            uint256 borrowAmount = calcBorrowAmount(orderedReserves);
            (uint256 amount0Out, uint256 amount1Out) =
                info.baseTokenSmaller ? (uint256(0), borrowAmount) : (borrowAmount, uint256(0));
            // borrow quote token on lower price pool, calculate how much debt we need to pay demoninated in base token
            uint256 debtAmount = getAmountIn(borrowAmount, orderedReserves.a1, orderedReserves.b1);
            // sell borrowed quote token on higher price pool, calculate how much base token we can get
            uint256 baseTokenOutAmount = getAmountOut(borrowAmount, orderedReserves.b2, orderedReserves.a2);
            info.debtTokenOutAmount = baseTokenOutAmount;
            info.borrowedAmount = borrowAmount;
            require(baseTokenOutAmount > debtAmount, 'Arbitrage fail, no profit');
            console.log('Profit:', (baseTokenOutAmount - debtAmount) / 1 ether);

            PoolAddress.PoolKey memory poolKey =
                PoolAddress.PoolKey({token0: info.baseToken, token1: info.quoteToken, fee: orderedReserves.fee0});
            // can only initialize this way to avoid stack too deep error
            FlashCallbackData memory callbackData;
            callbackData.amount0 = amount0Out;
            callbackData.amount1 = amount1Out;
            callbackData.payer = msg.sender;
            callbackData.poolKey = poolKey;
            callbackData.poolFee2 = orderedReserves.fee1;
            callbackData.poolFee3 = 0;
        
            IUniswapV3Pool pool = IUniswapV3Pool(info.lowerPool);
            address factory = pool.factory();
            require(pool == IUniswapV3Pool(PoolAddress.computeAddress(factory, poolKey)), "Pool not match");
            // recipient of borrowed amounts
            // amount of token0 requested to borrow
            // amount of token1 requested to borrow
            // need amount 0 and amount1 in callback to pay back pool
            // recipient of flash should be THIS contract
            pool.flash(address(this), amount0Out, amount1Out, abi.encode(callbackData));
        }

        uint256 balanceAfter = IERC20(info.baseToken).balanceOf(address(this));
        require(balanceAfter > balanceBefore, 'Losing money');

        if (info.baseToken == WETH9) {
            IWETH9(info.baseToken).withdraw(balanceAfter);
        }
        permissionedPairAddress = address(1);
    }

    /// @param fee0 The fee from calling flash for token0
    /// @param fee1 The fee from calling flash for token1
    /// @param data The data needed in the callback passed as FlashCallbackData from `initFlash`
    /// @notice implements the callback called from flash
    /// @dev fails if the flash is not profitable, meaning the amountOut from the flash is less than the amount borrowed
    function uniswapV3FlashCallback(
        uint256 fee0,
        uint256 fee1,
        bytes calldata data
    ) external override {
        ArbitrageInfo memory info;
        FlashCallbackData memory decoded = abi.decode(data, (FlashCallbackData));
        address factory = IUniswapV3Pool(info.lowerPool).factory();
        CallbackValidation.verifyCallback(factory, decoded.poolKey);

        address token0 = decoded.poolKey.token0;
        address token1 = decoded.poolKey.token1;
        
        IUniswapV3Pool targetPool = IUniswapV3Pool(info.higherPool);

        TransferHelper.safeTransfer(info.quoteToken, info.higherPool, info.borrowedAmount);
        
        (uint256 amountOut0, uint256 amountOut1, bool zeroForOne) =
            info.baseTokenSmaller ? (info.debtTokenOutAmount, uint256(0),false) : (uint256(0), info.debtTokenOutAmount, true);

        targetPool.swap(address(this), zeroForOne, int256(info.debtTokenOutAmount), 0, new bytes(0));
        

        // end up with amountOut0 of token0 from first swap and amountOut1 of token1 from second swap
        uint256 amount0Owed = LowGasSafeMath.add(decoded.amount0, fee0);
        uint256 amount1Owed = LowGasSafeMath.add(decoded.amount1, fee1);

        TransferHelper.safeApprove(token0, address(this), amount0Owed);
        TransferHelper.safeApprove(token1, address(this), amount1Owed);

        if (amount0Owed > 0) pay(token0, address(this), msg.sender, amount0Owed);
        if (amount1Owed > 0) pay(token1, address(this), msg.sender, amount1Owed);

        // if profitable pay profits to payer
        if (amountOut0 > amount0Owed) {
            uint256 profit0 = LowGasSafeMath.sub(amountOut0, amount0Owed);

            TransferHelper.safeApprove(token0, address(this), profit0);
            pay(token0, address(this), decoded.payer, profit0);
        }
        if (amountOut1 > amount1Owed) {
            uint256 profit1 = LowGasSafeMath.sub(amountOut1, amount1Owed);
            TransferHelper.safeApprove(token0, address(this), profit1);
            pay(token1, address(this), decoded.payer, profit1);
        }
    }

    /// @notice Calculate how much profit we can by arbitraging between two pools
    function getProfit(address pool0, address pool1) external view returns (uint256 profit, address baseToken) {
        (bool baseTokenSmaller, , ) = isbaseTokenSmaller(pool0, pool1);
        baseToken = baseTokenSmaller ? IUniswapV3Pool(pool0).token0() : IUniswapV3Pool(pool0).token1();

        (, , OrderedReserves memory orderedReserves) = getOrderedReserves(pool0, pool1, baseTokenSmaller);

        uint256 borrowAmount = calcBorrowAmount(orderedReserves);
        // borrow quote token on lower price pool,
        uint256 debtAmount = getAmountIn(borrowAmount, orderedReserves.a1, orderedReserves.b1);
        // sell borrowed quote token on higher price pool
        uint256 baseTokenOutAmount = getAmountOut(borrowAmount, orderedReserves.b2, orderedReserves.a2);
        uint256 amountOut = baseTokenOutAmount - (baseTokenOutAmount * (orderedReserves.fee1/1000000));
        uint256 debt = debtAmount + (debtAmount * (orderedReserves.fee0/1000000));
        if (amountOut < debt) {
            profit = 0;
        } else {
            profit = (amountOut - debt)/ 1 ether;
        }
    }

    /// @dev calculate the maximum base asset amount to borrow in order to get maximum profit during arbitrage
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

    // copy from UniswapV2Library
    // given an output amount of an asset and pair reserves, returns a required input amount of the other asset
    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountIn) {
        require(amountOut > 0, 'UniswapV3Library: INSUFFICIENT_OUTPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV3Library: INSUFFICIENT_LIQUIDITY');
        uint256 numerator = reserveIn.mul(amountOut).mul(1000);
        uint256 denominator = reserveOut.sub(amountOut).mul(997);
        amountIn = (numerator / denominator).add(1);
    }

    // copy from UniswapV2Library
    // given an input amount of an asset and pair reserves, returns the maximum output amount of the other asset
    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) internal pure returns (uint256 amountOut) {
        require(amountIn > 0, 'UniswapV3Library: INSUFFICIENT_INPUT_AMOUNT');
        require(reserveIn > 0 && reserveOut > 0, 'UniswapV3Library: INSUFFICIENT_LIQUIDITY');
        uint256 amountInWithFee = amountIn.mul(997);
        uint256 numerator = amountInWithFee.mul(reserveOut);
        uint256 denominator = reserveIn.mul(1000).add(amountInWithFee);
        amountOut = numerator / denominator;
    }
}
