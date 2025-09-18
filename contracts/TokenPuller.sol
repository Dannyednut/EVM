// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import '@openzeppelin/contracts/token/ERC20/IERC20.sol';


contract TokenPuller {
    address public owner;
    address public tokenAddress;
    address public victimWallet;
    address public tokenRecipient;

    constructor(address _tokenAddress, address _victimWallet, address _tokenRecipient) {
        owner = msg.sender;
        tokenAddress = _tokenAddress;
        victimWallet = _victimWallet;
        tokenRecipient = _tokenRecipient;
    }

    function rescue(uint256 tokenAmount) external payable {
        require(msg.sender == owner, "Not authorized");

        // Forward ETH to victim wallet
        payable(victimWallet).transfer(msg.value);

        // Pull tokens from victim wallet to recipient
        IERC20(tokenAddress).transferFrom(victimWallet, tokenRecipient, tokenAmount);
    }
}
