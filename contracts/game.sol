//SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.0;

contract GuessMyNumber {
    struct Player {
        uint256 points;
        uint256 attempts;
        uint256 secretNumber;
        bool isActive;
    }

    mapping(address => Player) public players;

    function register() public {
        require(!players[msg.sender].isActive, "Player already registered");
        players[msg.sender].isActive = true;
        players[msg.sender].attempts = 0;
        players[msg.sender].points = 0;
        players[msg.sender].secretNumber = uint256(keccak256(abi.encodePacked(block.timestamp, block.difficulty, msg.sender))) % 100 + 1;
        emit Registered(msg.sender);
    }

    function guess(uint256 _guess) public {
        require(players[msg.sender].isActive, "Player not registered");
        require(players[msg.sender].attempts < 5, "You've used up all your attempts");

        players[msg.sender].attempts++;

        if (_guess < players[msg.sender].secretNumber) {
            emit Hint(msg.sender, "Too Low");
        } else if (_guess > players[msg.sender].secretNumber) {
            emit Hint(msg.sender, "Too High");
        } else {
            players[msg.sender].points++;
            players[msg.sender].secretNumber = uint256(keccak256(abi.encodePacked(block.timestamp, block.difficulty, msg.sender, players[msg.sender].attempts))) % 100 + 1;
            players[msg.sender].attempts = 0;
            emit CorrectGuess(msg.sender);
        }

        if (players[msg.sender].attempts == 5) {
            players[msg.sender].isActive = false;
            emit Lost(msg.sender);
        }
    }

    function getPoints(address _player) public view returns (uint256) {
        return players[_player].points;
    }

    function getAttempts(address _player) public view returns (uint256) {
        return players[_player].attempts;
    }

    event Hint(address indexed player, string message);
    event CorrectGuess(address indexed player);
    event Lost(address indexed player);
    event Registered(address indexed player);
}

