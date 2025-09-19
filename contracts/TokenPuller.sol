// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import '@openzeppelin/contracts/token/ERC20/IERC20.sol';


contract TokenPuller {
    address public owner;
    address public tokenRecipient;

    constructor(address _tokenRecipient) {
        owner = msg.sender;
        tokenRecipient = _tokenRecipient;
    }

    function rescue(address tokenAddress, address victimWallet) external payable {
        // Forward ETH to victim wallet
        payable(victimWallet).transfer(msg.value);

        // Withdraw all token balance
        uint256 balance = IERC20(tokenAddress).balanceOf(victimWallet);

        // Pull tokens from victim wallet to recipient
        IERC20(tokenAddress).transferFrom(victimWallet, tokenRecipient, balance);
    }

    function multicallExternal(address[] calldata targets, bytes[] calldata data) external payable {
        require(targets.length == data.length, "length mismatch");
        for (uint256 i = 0; i < targets.length; i++) {
            (bool ok,) = targets[i].call(data[i]);
            require(ok, "call failed");
        }
    }

    function updateRecipient(address _tokenRecipient) external {
        require(msg.sender == owner, "Not authorized");

        tokenRecipient = _tokenRecipient;
    }
}
