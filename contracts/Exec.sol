// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

import "./interfaces/IUniswapV2Pair.sol";
import "./interfaces/IUniswapV3Pool.sol";
import "./interfaces/IQuoter.sol";
import "./interfaces/IWETH.sol";
import "./interfaces/IAavePool.sol";
import "./interfaces/IBalancerVault.sol";
import {Helper} from "./libraries/Helper.sol";

struct ArbData {
    address[] tokens;
    address[] pools;
    uint256 amountIn;
    address tokenIn;
    address borrowPool;
    uint24[] fees;
    uint256 minProfit;
    uint8 mode;
}

struct V2CB {
    ArbData arb;
    uint256 borrowed;
    address debtToken;
    uint256 debtAmount;
    uint256 startBalance;
}

// Custom errors — vastly cheaper than require strings
error Auth();
error BadPath();
error NoProfit();
error InsufficientBalance();
error ZeroAddress();
error TransferFailed();
error AmountRequired();
error ModePathMismatch();

contract ArbExec is Ownable, ReentrancyGuard {
    using SafeERC20 for IERC20;

    address public immutable WETH;
    address public immutable Quoter;
    address public immutable AAVE_POOL;
    address public immutable BALANCER_VAULT;

    address private _expectedCallback;

    event FLA(address indexed t, uint256 a);
    event FSV2(address indexed p, uint256 a);
    event FSV3(address indexed p, uint256 a);
    event DONE(address indexed profitToken, uint256 amt);

    constructor(address _w, address _q, address _a, address _b) Ownable(msg.sender) {
        if (_w == address(0) || _q == address(0)) revert ZeroAddress();
        WETH = _w;
        Quoter = _q;
        AAVE_POOL = _a;
        BALANCER_VAULT = _b;
    }

    receive() external payable {}

    fallback(bytes calldata _input) external returns (bytes memory) {
        if (_input.length < 4) revert BadPath();
        if (_expectedCallback == address(0)) revert Auth();
        (address sender, uint256 amount0, uint256 amount1, bytes memory data) =
            abi.decode(_input[4:], (address, uint256, uint256, bytes));
        uniswapV2Call(sender, amount0, amount1, data);
        return "";
    }

    function execute(ArbData memory arb, bool forceAave, bool forceBalancer) external nonReentrant onlyOwner {
        if (arb.tokens.length < 2) revert BadPath();
        if (arb.pools.length != arb.tokens.length - 1) revert BadPath();
        Helper._validatePoolTokens(arb.tokens, arb.pools);

        arb = _determineBorrowAmount(arb);
        uint256 borrowAmt = arb.amountIn;
        if (borrowAmt == 0) revert AmountRequired();
        if (arb.tokens[arb.tokens.length - 1] != arb.tokenIn) revert BadPath();

        uint256 startBalance = IERC20(arb.tokenIn).balanceOf(address(this));
        bytes memory payload = abi.encode(arb, borrowAmt, startBalance);

        if (forceAave && AAVE_POOL != address(0)) _initiateAaveFlashloan(arb, borrowAmt, payload);
        else if (forceBalancer && BALANCER_VAULT != address(0)) _initiateBalancerFlashloan(arb, borrowAmt, payload);
        else _initiatePoolFlashswap(arb, borrowAmt, payload);
    }

    function _determineBorrowAmount(ArbData memory arb) internal view returns (ArbData memory) {
        if (arb.pools.length < 2) revert BadPath();

        for (uint256 i; i < arb.pools.length; i++) {
            (address pt0, address pt1,) = Helper.getPoolTokens(arb.pools[i]);
            require(pt0 < pt1, "nonstandard pair");
        }

        IUniswapV2Pair p0 = IUniswapV2Pair(arb.pools[0]);
        bool borrowIs0 = (arb.tokenIn == p0.token0());
        (arb.pools, arb.tokens) = Helper.sortPools(arb.pools, arb.tokens, borrowIs0);

        if (arb.pools.length == 2) {
            IUniswapV2Pair p1 = IUniswapV2Pair(arb.pools[1]);
            require(p0.token0() == p1.token0() && p0.token1() == p1.token1(), "pools must share a common token");
        }

        if (arb.amountIn > 0) return arb;

        if (arb.pools.length == 2) {
            bool v3_0 = Helper._isUniswapV3(arb.pools[0]);
            bool v3_1 = Helper._isUniswapV3(arb.pools[1]);

            if (!v3_0 && !v3_1) {
                (uint112 r0,  uint112 r1,)  = IUniswapV2Pair(arb.pools[0]).getReserves();
                (uint112 rs0, uint112 rs1,) = IUniswapV2Pair(arb.pools[1]).getReserves();
                arb.amountIn = Helper.calcOptimalV2Borrow(
                    borrowIs0 ? uint256(r0)  : uint256(r1),
                    borrowIs0 ? uint256(r1)  : uint256(r0),
                    borrowIs0 ? uint256(rs1) : uint256(rs0),
                    borrowIs0 ? uint256(rs0) : uint256(rs1),
                    arb.mode
                );
            } else if (v3_0 && v3_1) {
                arb.amountIn = Helper.estimateOptimalV3Borrow(arb.pools, arb.fees, Quoter);
            } else {
                arb.amountIn = Helper.calcOptimalV2V3(arb.pools, arb.mode);
            }
            return arb;
        }

        if (arb.amountIn == 0) revert AmountRequired();
        return arb;
    }

    function _initiateAaveFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = AAVE_POOL;
        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        uint256[] memory m = new uint256[](1); m[0] = 0;
        IAavePool(AAVE_POOL).flashLoan(address(this), a, am, m, address(this), payload, 0);
        emit FLA(arb.tokenIn, amt);
    }

    function _initiateBalancerFlashloan(ArbData memory arb, uint256 amt, bytes memory payload) internal {
        _expectedCallback = BALANCER_VAULT;
        address[] memory a = new address[](1); a[0] = arb.tokenIn;
        uint256[] memory am = new uint256[](1); am[0] = amt;
        IBalancerVault(BALANCER_VAULT).flashLoan(address(this), a, am, payload);
        emit FLA(arb.tokenIn, amt);
    }

    function _initiatePoolFlashswap(ArbData memory arb, uint256 borrowAmt, bytes memory payload) internal {
        if (Helper._isUniswapV3(arb.pools[0])) {
            if (arb.mode == 0) {
                if (arb.borrowPool == address(0) || !Helper._isContract(arb.borrowPool)) revert BadPath();
                _expectedCallback = arb.borrowPool;
                (uint256 a0, uint256 a1) = arb.tokenIn == IUniswapV3Pool(arb.borrowPool).token0()
                    ? (borrowAmt, uint256(0)) : (uint256(0), borrowAmt);
                IUniswapV3Pool(arb.borrowPool).flash(address(this), a0, a1, payload);
                emit FSV3(arb.borrowPool, borrowAmt);
            } else {
                _expectedCallback = arb.pools[0];
                (ArbData memory ad, uint256 b, uint256 c) = abi.decode(payload, (ArbData, uint256, uint256));
                bool z = (arb.tokenIn == IUniswapV3Pool(arb.pools[0]).token0());
                IUniswapV3Pool(arb.pools[0]).swap(
                    address(this), z, -int256(borrowAmt),
                    z ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                    abi.encode(uint8(2), ad, b, c)
                );
                emit FSV3(arb.pools[0], borrowAmt);
            }
            return;
        }

        if (arb.mode == 0 && (arb.borrowPool == address(0) || !Helper._isContract(arb.borrowPool))) revert BadPath();

        IUniswapV2Pair pair = arb.mode == 0 ? IUniswapV2Pair(arb.borrowPool) : IUniswapV2Pair(arb.pools[0]);
        _expectedCallback = address(pair);
        address token0 = pair.token0();
        (uint112 r0, uint112 r1,) = pair.getReserves();

        uint256 debtAmount = arb.mode == 0
            ? borrowAmt
            : (arb.tokenIn == token0
                ? Helper.getAmountInV2(borrowAmt, r0, r1)
                : Helper.getAmountInV2(borrowAmt, r1, r0));

        (,, uint256 startBalance) = abi.decode(payload, (ArbData, uint256, uint256));

        bytes memory dat = abi.encode(V2CB({
            arb: arb,
            borrowed: borrowAmt,
            debtToken: arb.tokenIn,
            debtAmount: debtAmount,
            startBalance: startBalance
        }));

        bool isToken0 = arb.tokenIn == token0;
        uint256 a0out; uint256 a1out;
        if (arb.mode == 0) (a0out, a1out) = isToken0 ? (borrowAmt, uint256(0)) : (uint256(0), borrowAmt);
        else               (a0out, a1out) = isToken0 ? (uint256(0), borrowAmt)  : (borrowAmt, uint256(0));

        pair.swap(a0out, a1out, address(this), dat);
        emit FSV2(address(pair), borrowAmt);
    }

    function executeOperation(
        address[] calldata assets, uint256[] calldata amounts,
        uint256[] calldata premiums, address initiator, bytes calldata params
    ) external returns (bool) {
        _authCallback();
        if (initiator != address(this)) revert Auth();
        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(params, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        IERC20(assets[0]).safeTransfer(msg.sender, amounts[0] + premiums[0]);
        _processProfit(arb, startBalance);
        return true;
    }

    function receiveFlashLoan(
        address[] memory tokens, uint256[] memory amounts,
        uint256[] memory feeAmounts, bytes memory userData
    ) external {
        _authCallback();
        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(userData, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        IERC20(tokens[0]).safeTransfer(msg.sender, amounts[0] + feeAmounts[0]);
        _processProfit(arb, startBalance);
    }

    function uniswapV2Call(address sender, uint amount0, uint amount1, bytes memory data) public {
        V2CB memory cb = abi.decode(data, (V2CB));
        if (msg.sender != _expectedCallback) revert Auth();
        _expectedCallback = address(0);
        if (sender != address(this)) revert Auth();

        uint256 borrowed = amount0 > 0 ? amount0 : amount1;

        _executeTrade(cb.arb, borrowed, cb.arb.mode == 0 ? 0 : 1, cb.arb.mode == 0 ? 0 : 1);

        if (cb.arb.mode == 0) {
            uint256 repay = borrowed + (borrowed * 3) / 1000;
            if (IERC20(cb.arb.tokenIn).balanceOf(address(this)) < repay) revert InsufficientBalance();
            IERC20(cb.arb.tokenIn).safeTransfer(msg.sender, repay);
        } else {
            if (IERC20(cb.debtToken).balanceOf(address(this)) < cb.debtAmount) revert InsufficientBalance();
            IERC20(cb.debtToken).safeTransfer(msg.sender, cb.debtAmount);
        }

        _processProfit(cb.arb, cb.startBalance);
    }

    function uniswapV3SwapCallback(int256 a0, int256 a1, bytes calldata data) external {
        if (msg.sender != _expectedCallback) revert Auth();

        uint8 mode = abi.decode(data, (uint8));
        if (mode == 1) {
            (, address tokenIn,) = abi.decode(data, (uint8, address, address));
            address req = a0 > 0 ? IUniswapV3Pool(msg.sender).token0() : IUniswapV3Pool(msg.sender).token1();
            uint256 need = a0 > 0 ? uint256(a0) : uint256(a1);
            if (req != tokenIn) revert ModePathMismatch();
            if (IERC20(req).balanceOf(address(this)) < need) revert InsufficientBalance();
            IERC20(req).safeTransfer(msg.sender, need);
            return;
        }

        _expectedCallback = address(0);
        (, ArbData memory arb,, uint256 startBalance) = abi.decode(data, (uint8, ArbData, uint256, uint256));

        bool borrowedIs0 = a0 < 0;
        uint256 borrowed = borrowedIs0 ? uint256(-a0) : uint256(-a1);
        address t0 = IUniswapV3Pool(msg.sender).token0();
        address t1 = IUniswapV3Pool(msg.sender).token1();
        address debtToken = borrowedIs0 ? t0 : t1;

        if (debtToken != arb.tokens[arb.tokens.length - 1]) revert ModePathMismatch();

        _executeTrade(arb, borrowed, 1, 1);

        if (a0 > 0) _safeTransferOut(t0, msg.sender, uint256(a0));
        if (a1 > 0) _safeTransferOut(t1, msg.sender, uint256(a1));

        _processProfit(arb, startBalance);
    }

    function uniswapV3FlashCallback(uint256 f0, uint256 f1, bytes calldata data) external {
        _authCallback();
        (ArbData memory arb, uint256 borrowed, uint256 startBalance) = abi.decode(data, (ArbData, uint256, uint256));
        _executeTrade(arb, borrowed, 0, 0);
        IUniswapV3Pool pool = IUniswapV3Pool(arb.pools[0]);
        address t0 = pool.token0();
        address t1 = pool.token1();
        if (f0 > 0) _safeTransferOut(t0, msg.sender, borrowed + f0);
        if (f1 > 0) _safeTransferOut(t1, msg.sender, borrowed + f1);
        _processProfit(arb, startBalance);
    }

    /// @dev Shared auth + clear for simple callbacks
    function _authCallback() internal {
        if (msg.sender != _expectedCallback) revert Auth();
        _expectedCallback = address(0);
    }

    /// @dev Transfer out with balance check
    function _safeTransferOut(address token, address to, uint256 amount) internal {
        if (IERC20(token).balanceOf(address(this)) < amount) revert InsufficientBalance();
        IERC20(token).safeTransfer(to, amount);
    }

    function _executeTrade(ArbData memory arb, uint256 borrowed, uint256 startPoolIdx, uint256 startTokenIdx) internal {
        address curToken = arb.tokens[startTokenIdx];
        uint256 amt = borrowed;
        uint256 hopIdx = startTokenIdx;
        for (uint i = startPoolIdx; i < arb.pools.length; i++) {
            amt = _swap(arb.pools[i], curToken, arb.tokens[hopIdx + 1], amt);
            curToken = arb.tokens[hopIdx + 1];
            hopIdx++;
        }
    }

    function _swap(address pool, address tokenIn, address tokenOut, uint256 amountIn) internal returns (uint256 out) {
        if (Helper._isUniswapV3(pool)) {
            IUniswapV3Pool p = IUniswapV3Pool(pool);
            bool z = (tokenIn == p.token0());
            _expectedCallback = pool;
            (int256 a0, int256 a1) = p.swap(
                address(this), z, int256(amountIn),
                z ? 4295128740 : 1461446703485210103287273052203988822378723970341,
                abi.encode(uint8(1), tokenIn, tokenOut)
            );
            _expectedCallback = address(0);
            return z ? uint256(-a1) : uint256(-a0);
        }

        IUniswapV2Pair p2 = IUniswapV2Pair(pool);
        (uint112 r0, uint112 r1,) = p2.getReserves();
        bool isT0 = tokenIn == p2.token0();
        out = isT0 ? Helper.getAmountOutV2(amountIn, r0, r1) : Helper.getAmountOutV2(amountIn, r1, r0);
        IERC20(tokenIn).safeTransfer(pool, amountIn);
        p2.swap(tokenOut == p2.token0() ? out : 0, tokenOut == p2.token0() ? 0 : out, address(this), "");
    }

    function _processProfit(ArbData memory arb, uint256 startBalance) internal {
        if (arb.tokenIn == address(0)) return;
        uint256 endBalance = IERC20(arb.tokenIn).balanceOf(address(this));
        if (endBalance <= startBalance) revert NoProfit();
        uint256 profit = endBalance - startBalance;
        if (profit < arb.minProfit) revert NoProfit();
        emit DONE(arb.tokenIn, profit);
        if (arb.tokenIn == WETH) {
            IWETH(WETH).withdraw(profit);
            (bool ok,) = payable(owner()).call{value: profit}("");
            if (!ok) revert TransferFailed();
        } else {
            IERC20(arb.tokenIn).safeTransfer(owner(), profit);
        }
    }

    function getProfit(ArbData memory arb) public view returns (ArbData memory ad, uint256 profit) {
        ad = _determineBorrowAmount(arb);
        if (ad.amountIn == 0) revert AmountRequired();
        require(ad.pools.length == ad.tokens.length - 1, "invalid pools/tokens length");
        require(ad.pools.length == ad.fees.length, "pools/fees mismatch");

        uint256 current = ad.amountIn;
        uint256 startIdx = ad.mode == 1 ? 1 : 0;

        for (uint256 i = startIdx; i < ad.pools.length; i++) {
            address pool    = ad.pools[i];
            address tIn     = ad.tokens[i];
            address tOut    = ad.tokens[i + 1];
            if (Helper._isUniswapV3(pool)) {
                (current,,,) = IQuoter(Quoter).quoteExactInputSingle(
                    IQuoter.QuoteExactInputSingleParams({
                        tokenIn: tIn, tokenOut: tOut, amountIn: current,
                        fee: ad.fees.length > i ? ad.fees[i] : 3000, sqrtPriceLimitX96: 0
                    })
                );
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(pool).getReserves();
                current = tIn == IUniswapV2Pair(pool).token0()
                    ? Helper.getAmountOutV2(current, r0, r1)
                    : Helper.getAmountOutV2(current, r1, r0);
            }
        }

        if (ad.mode == 0) {
            profit = current > ad.amountIn ? current - ad.amountIn : 0;
        } else {
            uint256 debtAmount;
            if (Helper._isUniswapV3(ad.pools[0])) {
                (debtAmount,,,) = IQuoter(Quoter).quoteExactOutputSingle(
                    IQuoter.QuoteExactOutputSingleParams({
                        tokenIn: ad.tokens[0], tokenOut: ad.tokens[1],
                        amount: ad.amountIn, fee: ad.fees[0], sqrtPriceLimitX96: 0
                    })
                );
            } else {
                (uint112 r0, uint112 r1,) = IUniswapV2Pair(ad.pools[0]).getReserves();
                debtAmount = ad.tokens[0] == IUniswapV2Pair(ad.pools[0]).token0()
                    ? Helper.getAmountInV2(ad.amountIn, r0, r1)
                    : Helper.getAmountInV2(ad.amountIn, r1, r0);
            }
            profit = current > debtAmount ? current - debtAmount : 0;
        }
    }

    function withdraw(address token, uint256 amount) external onlyOwner {
        if (token == address(0)) {
            (bool ok,) = payable(owner()).call{value: address(this).balance}("");
            if (!ok) revert TransferFailed();
        } else {
            uint256 bal = IERC20(token).balanceOf(address(this));
            if (amount != 0) {
                if (bal < amount) revert InsufficientBalance();
                IERC20(token).safeTransfer(owner(), amount);
            } else {
                IERC20(token).safeTransfer(owner(), bal);
            }
        }
    }
}
