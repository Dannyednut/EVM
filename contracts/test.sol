// SPDX-License-Identifier: Unlicense
pragma solidity <=0.8.20;
pragma abicoder v2;

import '@openzeppelin/contracts/token/ERC20/IERC20.sol';
import '@openzeppelin/contracts/token/ERC20/SafeERC20.sol';
import '@openzeppelin/contracts/access/Ownable.sol';
import '@openzeppelin/contracts/utils/EnumerableSet.sol';
import '@uniswap/v3-core/contracts/interfaces/IUniswapV3Pool.sol';
import '@uniswap/v3-periphery/contracts/interfaces/ISwapRouter.sol';
import '@uniswap/v3-periphery/contracts/libraries/PoolAddress.sol';


import './libraries/Decimal.sol';
import './interfaces/IWETH9.sol';

struct ArbitrageInfo {
    address baseToken;
    address quoteToken;
    bool baseTokenSmaller;
    IUniswapV3Pool lowerPool; // pool with lower price, denominated in quote asset
    IUniswapV3Pool higherPool; // pool with higher price, denominated in quote asset
}

struct FlashCallbackData {
    uint256 amount0;
    uint256 amount1;
    address payer;
    PoolAddress.PoolKey poolKey;
    uint24 poolFee2;
    uint24 poolFee3;
}

contract FlashBot is Ownable {
    using SafeERC20 for IERC20;
    using EnumerableSet for EnumerableSet.AddressSet;

    ISwapRouter public immutable swapRouter;
    address immutable WETH;

    EnumerableSet.AddressSet baseTokens;

    event Withdrawn(address indexed to, uint256 indexed value);
    event BaseTokenAdded(address indexed token);
    event BaseTokenRemoved(address indexed token);

    constructor(address _WETH, ISwapRouter _swapRouter) Ownable(msg.sender) {
        WETH = _WETH;
        swapRouter = _swapRouter;
        baseTokens.add(_WETH);
    }

    receive() external payable {}

    /// @dev Redirect uniswap callback function
    /// The callback function on different DEX are not same, so use a fallback to redirect to uniswapV2Call
    fallback(bytes calldata _input) external returns (bytes memory) {
        (address sender, uint256 amount0, uint256 amount1, bytes memory data) = abi.decode(_input[4:], (address, uint256, uint256, bytes));
        ArbitrageInfo memory info;
        uniswapV3FlashCallback(sender, amount0, amount1, data,info);

        return "";
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
            IERC20(token).transfer(owner(), balance);
        }
        baseTokens.remove(token);
        emit BaseTokenRemoved(token);
    }

    function flashArbitrage(
        address pool0,
        address pool1,
        uint256 amount0,
        uint256 amount1,
        uint24 fee0,
        uint24 fee1
    ) external {
        ArbitrageInfo memory info;
        // Logic to determine which pool has the lower price and perform the flash loan
        // This will involve calling the flash function on the lower price pool
        info.lowerPool = IUniswapV3Pool(pool0); // Assume pool0 is the lower price pool
        info.higherPool = IUniswapV3Pool(pool1); // Assume pool1 is the higher price pool

        // Initiate the flash loan from the lower price pool
        info.lowerPool.flash(
            address(this), // recipient of the borrowed tokens
            amount0, // amount of token0 to borrow
            amount1, // amount of token1 to borrow
            abi.encode(pool1, fee1) // encode the target pool and fee for the callback
        );
    }

    // This function will be called by the Uniswap V3 pool after the flash loan is executed
    function uniswapV3FlashCallback(
        address sender,
        uint256 amount0,
        uint256 amount1,
        bytes memory data,
        ArbitrageInfo memory info
    ) public {
        // Ensure the callback is coming from the correct pool
        require(msg.sender == address(info.lowerPool), "Unauthorized callback");
        require(sender == address(this), 'Not from this contract');

        // Decode the data to get the target pool and fee
        FlashCallbackData memory decoded = abi.decode(data, (FlashCallbackData));

        // Perform the swap on the higher price pool
        // Here we assume that amount0 and amount1 are the amounts borrowed
        // You will need to determine which token is being borrowed and which is being sold
        // For example, if amount0 is borrowed, we sell it in the target pool
        if (amount0 > 0) {
            // Swap borrowed token0 for token1 in the target pool
            swapRouter.exactInputSingle(
                ISwapRouter.ExactInputSingleParams({
                    tokenIn: info.lowerPool.token0(),
                    tokenOut: info.lowerPool.token1(),
                    fee: fee,
                    recipient: address(this),
                    deadline: block.timestamp,
                    amountIn: amount0,
                    amountOutMinimum: 0, // Set to 0 for simplicity; implement slippage checks as needed
                    sqrtPriceLimitX96: 0
                })
            );
        } else if (amount1 > 0) {
            // Swap borrowed token1 for token0 in the target pool
            swapRouter.exactInputSingle(
                ISwapRouter.ExactInputSingleParams({
                    tokenIn: info.lowerPool.token1(),
                    tokenOut: info.lowerPool.token0(),
                    fee: fee,
                    recipient: address(this),
                    deadline: block.timestamp,
                    amountIn: amount1,
                    amountOutMinimum: 0, // Set to 0 for simplicity; implement slippage checks as needed
                    sqrtPriceLimitX96: 0
                })
            );
        }

        // Calculate the amount owed back to the lower pool
        uint256 amountOwed0 = amount0 + (amount0 * 3 / 997); // Example fee calculation
        uint256 amountOwed1 = amount1 + (amount1 * 3 / 997); // Example fee calculation

        // Repay the flash loan
        IERC20(info.lowerPool.token0()).safeTransfer(msg.sender, amountOwed0);
        IERC20(info.lowerPool.token1()).safeTransfer(msg.sender, amountOwed1);
    }

    // Additional functions for profit calculation, etc., can be added here
}