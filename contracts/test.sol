// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Simple{
    uint256 public data = 1_000;

    function set(uint256 x) public {
        data = x;
    }

    function get() public view returns (uint256){
        return data;
    }
}