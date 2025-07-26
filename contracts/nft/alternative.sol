// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import "@openzeppelin/contracts/token/ERC721/extensions/ERC721Enumerable.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract MarketSentimentNFT is ERC721Enumerable, Ownable {
    enum Sentiment { VeryBearish, Bearish, Neutral, Bullish, VeryBullish }
    enum MarketPhase { Reversal, Consolidation, Trend, Volatile, Stable }

    struct Traits {
        string character;
        string mood;
        string background;
        string aura;
        string expression;
        string accessory;
        string weather;
    }

    mapping(uint256 => Traits) public tokenTraits;

    Sentiment public currentSentiment;
    MarketPhase public currentMarketPhase;
    uint256 public nextTokenId;

    constructor() ERC721("MarketSentimentNFT", "MSNFT") Ownable(msg.sender) {}

    // Public minting
    function mint(uint256 quantity) external {
        for (uint256 i = 0; i < quantity; i++) {
            uint256 tokenId = nextTokenId++;
            _safeMint(msg.sender, tokenId);
            _assignTraits(tokenId);
        }
    }

    // Owner sets market sentiment + phase
    function setMarketState(Sentiment sentiment, MarketPhase phase) external onlyOwner {
        currentSentiment = sentiment;
        currentMarketPhase = phase;
        _evolveAllTraits();
    }

    // Internal: Assign traits on mint
    function _assignTraits(uint256 tokenId) internal {
        tokenTraits[tokenId] = _generateTraits();
    }

    // Internal: Evolve traits based on current sentiment
    function _evolveAllTraits() internal {
        for (uint256 i = 0; i < totalSupply(); i++) {
            uint256 tokenId = tokenByIndex(i);
            tokenTraits[tokenId] = _generateTraits();
        }
    }

    // Internal: Logic to generate traits
    function _generateTraits() internal view returns (Traits memory traits) {
        if (currentSentiment == Sentiment.VeryBearish) {
            traits.character = "Bear";
            traits.mood = "Panicked";
            traits.background = "Crimson";
            traits.aura = "Red Flame";
            traits.expression = "Screaming";
            traits.accessory = "Broken Chains";
            traits.weather = "Thunderstorm";
        } else if (currentSentiment == Sentiment.Bearish) {
            traits.character = "Bear";
            traits.mood = "Cautious";
            traits.background = "Dark Gray";
            traits.aura = "Smoke";
            traits.expression = "Worried";
            traits.accessory = "Shield";
            traits.weather = "Rain";
        } else if (currentSentiment == Sentiment.Neutral) {
            traits.character = "Observer";
            traits.mood = "Calm";
            traits.background = "Blue Gray";
            traits.aura = "Balance Field";
            traits.expression = "Neutral";
            traits.accessory = "Scroll";
            traits.weather = "Cloudy";
        } else if (currentSentiment == Sentiment.Bullish) {
            traits.character = "Bull";
            traits.mood = "Confident";
            traits.background = "Sky Blue";
            traits.aura = "Yellow Glow";
            traits.expression = "Smiling";
            traits.accessory = "Golden Horns";
            traits.weather = "Sunny";
        } else if (currentSentiment == Sentiment.VeryBullish) {
            traits.character = "Bull";
            traits.mood = "Euphoric";
            traits.background = "Gold";
            traits.aura = "Solar Flare";
            traits.expression = "Ecstatic";
            traits.accessory = "Wings";
            traits.weather = "Rainbow";
        }
    }

    // Metadata
    function tokenURI(uint256 tokenId) public view override returns (string memory) {
        Traits memory traits = tokenTraits[tokenId];
        string memory json = string(abi.encodePacked(
            '{"name": "MarketSentimentNFT #',
            _toString(tokenId),
            '", "description": "Dynamic NFT that evolves with market sentiment",',
            '"attributes": [',
                '{"trait_type": "Character", "value": "', traits.character, '"},',
                '{"trait_type": "Mood", "value": "', traits.mood, '"},',
                '{"trait_type": "Background", "value": "', traits.background, '"},',
                '{"trait_type": "Aura", "value": "', traits.aura, '"},',
                '{"trait_type": "Expression", "value": "', traits.expression, '"},',
                '{"trait_type": "Accessory", "value": "', traits.accessory, '"},',
                '{"trait_type": "Weather", "value": "', traits.weather, '"},',
                '{"trait_type": "Sentiment", "value": "', _sentimentToString(currentSentiment), '"},',
                '{"trait_type": "Market Phase", "value": "', _phaseToString(currentMarketPhase), '"}',
            ']}'
        ));
        return string(abi.encodePacked("data:application/json;utf8,", json));
    }

    function _sentimentToString(Sentiment s) internal pure returns (string memory) {
        if (s == Sentiment.VeryBearish) return "Very Bearish";
        if (s == Sentiment.Bearish) return "Bearish";
        if (s == Sentiment.Neutral) return "Neutral";
        if (s == Sentiment.Bullish) return "Bullish";
        return "Very Bullish";
    }

    function _phaseToString(MarketPhase p) internal pure returns (string memory) {
        if (p == MarketPhase.Reversal) return "Reversal";
        if (p == MarketPhase.Consolidation) return "Consolidation";
        if (p == MarketPhase.Trend) return "Trend";
        if (p == MarketPhase.Volatile) return "Volatile";
        return "Stable";
    }

    function _toString(uint256 value) internal pure returns (string memory) {
        if (value == 0) return "0";
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }
}