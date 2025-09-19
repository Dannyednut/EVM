// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Digest{

    function getDigest(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline
    ) public pure returns (bytes32) {
        bytes32 DOMAIN_SEPARATOR = 0xf0d9318d2993164b11acaed4adb312d72e2753ffe14818ae4d917d64931bf019;
        bytes32 structHash = keccak256(abi.encode(
            keccak256("Permit(address owner,address spender,uint256 value,uint256 deadline)"),
            owner,
            spender,
            value,
            deadline
        ));
        return keccak256(abi.encodePacked("\x19\x01", DOMAIN_SEPARATOR, structHash));
    }

}