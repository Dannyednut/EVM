// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import "https://github.com/chiru-labs/ERC721A/blob/main/contracts/ERC721A.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

event Minted(address indexed to, uint256 tokenId);
event TraitsAssigned(uint256 tokenId, string beastType);

contract CryptoBeasts is ERC721A, Ownable {
    enum SentimentLevel { VeryBearish, Bearish, Neutral, Bullish, VeryBullish }

    struct Traits {
        string beastType; // "Bull" or "Bear"
        string fur;
        string eyes;
        string background;
    }

    mapping(uint256 => Traits) public tokenTraits;
    uint256 public sentimentScore; // 0 - 100
    SentimentLevel public currentSentiment;

    constructor() ERC721A("Crypto Beasts", "CBEAST") Ownable(msg.sender){}

    function mint(uint256 quantity) external {
        uint256 startTokenId = _nextTokenId();
        _safeMint(msg.sender, quantity);

        for (uint256 i = 0; i < quantity; i++) {
            string memory beastType = (uint256(keccak256(abi.encodePacked(block.timestamp, msg.sender, i))) % 2 == 0)
                ? "Bull" : "Bear";

            uint256 tokenId = startTokenId + i;

            tokenTraits[tokenId] = Traits({
                beastType: beastType,
                fur: "Obsidian",
                eyes: "Emerald",
                background: "Golden Peak"
            });

            emit TraitsAssigned(tokenId, beastType);
            emit Minted(msg.sender, tokenId);
        }
    }

    function updateSentiment(uint256 newScore) external onlyOwner {
        require(newScore <= 100, "Max sentiment is 100");
        sentimentScore = newScore;

        if (newScore < 20) {
            currentSentiment = SentimentLevel.VeryBearish;
        } else if (newScore < 40) {
            currentSentiment = SentimentLevel.Bearish;
        } else if (newScore < 60) {
            currentSentiment = SentimentLevel.Neutral;
        } else if (newScore < 80) {
            currentSentiment = SentimentLevel.Bullish;
        } else {
            currentSentiment = SentimentLevel.VeryBullish;
        }
    }

    function debugToken(uint256 tokenId) public view returns (string memory, string memory, string memory, string memory) {
        Traits memory t = tokenTraits[tokenId];
        return (t.beastType, t.fur, t.eyes, t.background);
    }


    function tokenURI(uint256 tokenId) public view override returns (string memory) {
        require(_exists(tokenId), "Does not exist");

        Traits memory traits = tokenTraits[tokenId];
        string memory svg = generateSVG(traits);

        return string(abi.encodePacked(
            "data:application/json;utf8,{",
                '"name":"Crypto Beast #', _toString(tokenId), '",',
                '"description":"Sentient NFT that evolves with market sentiment.",',
                '"image":"data:image/svg+xml;utf8,', svg, '",',
                '"attributes":[',
                    '{"trait_type":"Type","value":"', traits.beastType, '"},',
                    '{"trait_type":"Fur","value":"', traits.fur, '"},',
                    '{"trait_type":"Eyes","value":"', traits.eyes, '"},',
                    '{"trait_type":"Background","value":"', traits.background, '"},',
                    '{"trait_type":"Sentiment","value":"', sentimentLevelToString(currentSentiment), '"}',
                ']',
            "}"
        ));
    }

    function generateSVG(Traits memory traits) internal view returns (string memory) {
        string memory color = sentimentColor(currentSentiment);

        return string(abi.encodePacked(
            "<svg xmlns='http://www.w3.org/2000/svg' width='300' height='300'>",
            "<rect width='100%' height='100%' fill='", color, "'/>",
            "<text x='50%' y='50%' dominant-baseline='middle' text-anchor='middle' font-size='24' fill='white'>",
            traits.beastType, "</text>",
            "</svg>"
        ));
    }

    function sentimentColor(SentimentLevel level) internal pure returns (string memory) {
        if (level == SentimentLevel.VeryBearish) return "#2c3e50";
        if (level == SentimentLevel.Bearish) return "#34495e";
        if (level == SentimentLevel.Neutral) return "#7f8c8d";
        if (level == SentimentLevel.Bullish) return "#27ae60";
        if (level == SentimentLevel.VeryBullish) return "#2ecc71";
        return "#000000";
    }

    function sentimentLevelToString(SentimentLevel level) internal pure returns (string memory) {
        if (level == SentimentLevel.VeryBearish) return "Very Bearish";
        if (level == SentimentLevel.Bearish) return "Bearish";
        if (level == SentimentLevel.Neutral) return "Neutral";
        if (level == SentimentLevel.Bullish) return "Bullish";
        if (level == SentimentLevel.VeryBullish) return "Very Bullish";
        return "Unknown";
    }
}
