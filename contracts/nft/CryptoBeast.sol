// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import "https://github.com/chiru-labs/ERC721A/blob/main/contracts/ERC721A.sol";
import "@openzeppelin/contracts/access/Ownable.sol";


contract CryptoBeasts is ERC721A, Ownable {

    enum SentimentLevel { VeryBearish, Bearish, Neutral, Bullish, VeryBullish }

    event TraitsEvolved(uint256 tokenId, string newFur, string newEyes, string newBackground);
    event BeastMinted(address owner, uint256 tokenId);
    event SentimentUpdated(uint256 newScore, SentimentLevel newSentiment);

    uint256 public lastUpdate;

    modifier cooldown() {
        require(block.timestamp >= lastUpdate + 10 minutes, "Cooldown active");
        _;
        lastUpdate = block.timestamp;
    }

    struct Traits {
        string beastType; // "Bull" or "Bear"
        string fur;
        string eyes;
        string background;
    }

    struct SentimentSnapshot {
        uint256 score;
        SentimentLevel level;
        uint256 timestamp;
    }

    SentimentSnapshot[] public sentimentHistory;
    mapping(uint256 => Traits) public tokenTraits;
    uint256 public sentimentScore; // 0 - 100
    address public oracle;

    function setOracle(address _oracle) external onlyOwner {
        oracle = _oracle;
    }
    SentimentLevel public currentSentiment;

    constructor() ERC721A("Crypto Beasts", "CBEAST") Ownable(msg.sender){}

    function getSentimentHistoryLength() external view returns (uint256) {
        return sentimentHistory.length;
    }

    function getSentimentSnapshot(uint256 index) external view returns (uint256, SentimentLevel, uint256) {
        require(index < sentimentHistory.length, "Invalid index");
        SentimentSnapshot memory snapshot = sentimentHistory[index];
        return (snapshot.score, snapshot.level, snapshot.timestamp);
    }

    function mint(uint256 quantity) external {
        uint256 startTokenId = _nextTokenId();
        _safeMint(msg.sender, quantity);

        for (uint256 i = 0; i < quantity; i++) {
            uint256 seed = uint256(keccak256(abi.encodePacked(block.timestamp, msg.sender, startTokenId + i)));

            string memory beastType = (seed % 2 == 0) ? "Bull" : "Bear";

            string[4] memory furs = ["Obsidian", "Snowy", "Flamecoat", "Azurehide"];
            string[4] memory eyes = ["Emerald", "Crimson", "Void", "Sapphire"];
            string[4] memory backgrounds = ["Golden Peak", "Stormrise", "Midnight Zone", "Arctic Glow"];

            string memory fur = furs[seed % furs.length];
            string memory eye = eyes[(seed >> 8) % eyes.length];
            string memory bg = backgrounds[(seed >> 16) % backgrounds.length];

            uint256 newItemId = startTokenId + i;
            tokenTraits[startTokenId + i] = Traits({
                beastType: beastType,
                fur: fur,
                eyes: eye,
                background: bg
            });
            emit BeastMinted(msg.sender, newItemId);
        }
        
    }

    function evolveTraits() internal {
        for (uint256 tokenId = 0; tokenId < _nextTokenId(); tokenId++) {
            Traits storage traits = tokenTraits[tokenId];

            // Evolve Fur based on sentiment
            if (currentSentiment == SentimentLevel.VeryBearish) {
                traits.fur = "Ashen";
                traits.eyes = "Dim Emerald";
                traits.background = "Fogveil";
            } else if (currentSentiment == SentimentLevel.Bearish) {
                traits.fur = "Shadow";
                traits.eyes = "Dull Crimson";
                traits.background = "Clouded Ridge";
            } else if (currentSentiment == SentimentLevel.Neutral) {
                traits.fur = "Obsidian";
                traits.eyes = "Emerald";
                traits.background = "Golden Peak";
            } else if (currentSentiment == SentimentLevel.Bullish) {
                traits.fur = "Brightgold";
                traits.eyes = "Glowing Amber";
                traits.background = "Sunrise Steppe";
            } else if (currentSentiment == SentimentLevel.VeryBullish) {
                traits.fur = "Radiant Flame";
                traits.eyes = "Blazing Sapphire";
                traits.background = "Aurora Zenith";
            }
            emit TraitsEvolved(tokenId, traits.fur, traits.eyes, traits.background);
        }
    }



    function updateSentiment(uint256 newScore) public  onlyOwner cooldown{
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

        if (_nextTokenId() == 0) return;
        evolveTraits(); // 🔁 trigger trait update across all tokens

        sentimentHistory.push(SentimentSnapshot({
            score: newScore,
            level: currentSentiment,
            timestamp: block.timestamp
        }));
        emit SentimentUpdated(newScore, currentSentiment);

    }

    function receiveSentimentScore(uint256 score) external {
        require(msg.sender == oracle, "Not authorized oracle");
        updateSentiment(score);
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

    function beastIcon(string memory beastType, SentimentLevel level) internal pure returns (string memory) {
        if (keccak256(bytes(beastType)) == keccak256("Bull")) {
            if (level == SentimentLevel.VeryBullish) return "Bull Up";
            if (level == SentimentLevel.Bullish) return "Bull";
            return "Bull Neutral";
        } else {
            if (level == SentimentLevel.VeryBearish) return "Bear Down";
            if (level == SentimentLevel.Bearish) return "Bear";
            return "Bear Neutral";
        }
    }

    function sentimentMood(SentimentLevel level, string memory /*beastType*/) internal pure returns (string memory) {
        if (level == SentimentLevel.VeryBullish || level == SentimentLevel.VeryBearish) return "Raging";
        if (level == SentimentLevel.Bullish || level == SentimentLevel.Bearish) return "Agitated";
        return "Calm";
    }



    function generateSVG(Traits memory traits) internal view returns (string memory) {
        string memory color = sentimentColor(currentSentiment);
        string memory mood = sentimentMood(currentSentiment, traits.beastType);
        string memory icon = beastIcon(traits.beastType, currentSentiment);

        return string(abi.encodePacked(
            "<svg xmlns='http://www.w3.org/2000/svg' width='300' height='300'>",
                "<rect width='100%' height='100%' fill='", color, "'/>",
                "<text x='50%' y='30%' dominant-baseline='middle' text-anchor='middle' font-size='20' fill='white'>", icon, "</text>",
                "<text x='50%' y='45%' dominant-baseline='middle' text-anchor='middle' font-size='14' fill='white'>Mood: ", mood, "</text>",
                "<text x='50%' y='60%' dominant-baseline='middle' text-anchor='middle' font-size='14' fill='white'>Fur: ", traits.fur, "</text>",
                "<text x='50%' y='70%' dominant-baseline='middle' text-anchor='middle' font-size='14' fill='white'>Eyes: ", traits.eyes, "</text>",
                "<text x='50%' y='80%' dominant-baseline='middle' text-anchor='middle' font-size='14' fill='white'>BG: ", traits.background, "</text>",
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

    function getLatestSentiment() external view returns (uint256, SentimentLevel, uint256) {
        if (sentimentHistory.length == 0) {
            return (0, SentimentLevel.Neutral, block.timestamp);
        }
        SentimentSnapshot memory snap = sentimentHistory[sentimentHistory.length - 1];
        return (snap.score, snap.level, snap.timestamp);
    }

}
