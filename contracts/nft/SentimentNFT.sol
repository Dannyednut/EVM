// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
// import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
// import "@openzeppelin/contracts/access/Ownable.sol";
// import "@openzeppelin/contracts/utils/Counters.sol";
// import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

import "https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v4.9.0/contracts/token/ERC721/ERC721.sol";
import "https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v4.9.0/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import "https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v4.9.0/contracts/access/Ownable.sol";
import "https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v4.9.0/contracts/utils/Counters.sol";
import "https://raw.githubusercontent.com/OpenZeppelin/openzeppelin-contracts/v4.9.0/contracts/security/ReentrancyGuard.sol";


contract SentimentNFT is ERC721, ERC721URIStorage, Ownable, ReentrancyGuard {
    using Counters for Counters.Counter;
    
    Counters.Counter private _tokenIds;
    
    // Oracle for market sentiment (0-1000 representing 0.0-1.0)
    address public sentimentOracle;
    uint256 public currentSentiment = 500; // Default to 0.5 (neutral)
    
    // Pricing parameters
    uint256 public constant BASE_PRICE = 0.01 ether;
    uint256 public constant MAX_SENTIMENT_MULTIPLIER = 3000; // 3x multiplier
    
    // Rarity tiers based on sentiment
    enum RarityTier { Common, Rare, UltraRare, Legendary }
    
    struct NFTMetadata {
        uint256 mintSentiment;
        uint256 currentSentiment;
        RarityTier rarity;
        uint256 mintTimestamp;
        string attributes;
    }
    
    mapping(uint256 => NFTMetadata) public nftMetadata;
    
    // Events
    event SentimentUpdated(uint256 newSentiment);
    event NFTMinted(uint256 tokenId, address to, uint256 sentiment, uint256 price);
    event NFTEvolved(uint256 tokenId, uint256 newSentiment, RarityTier newRarity);
    
    modifier onlyOracle() {
        require(msg.sender == sentimentOracle || msg.sender == owner(), "Not authorized oracle");
        _;
    }
    
    constructor() ERC721("SentimentNFT", "SNFT") {}
    
    /**
     * @dev Set the sentiment oracle address
     */
    function setSentimentOracle(address _oracle) external onlyOwner {
        sentimentOracle = _oracle;
    }
    
    /**
     * @dev Update market sentiment (called by oracle)
     * @param _sentiment New sentiment value (0-1000)
     */
    function updateSentiment(uint256 _sentiment) external onlyOracle {
        require(_sentiment <= 1000, "Sentiment must be <= 1000");
        currentSentiment = _sentiment;
        emit SentimentUpdated(_sentiment);
        
        // Update all existing NFTs' current sentiment
        _updateAllNFTSentiments(_sentiment);
    }
    
    /**
     * @dev Calculate current mint price based on sentiment
     */
    function getCurrentMintPrice() public view returns (uint256) {
        // Base price + (sentiment * 0.49 ETH) * sentiment multiplier
        uint256 sentimentPrice = BASE_PRICE + (currentSentiment * 49 ether / 100000);
        //uint256 multiplier = 1000 + (currentSentiment * 2); // 1x to 3x multiplier
        return sentimentPrice /1000; //* multiplier / 1000;
    }
    
    /**
     * @dev Get rarity tier based on sentiment
     */
    function getRarityTier(uint256 sentiment) public pure returns (RarityTier) {
        if (sentiment > 800) return RarityTier.Legendary;
        if (sentiment > 600) return RarityTier.UltraRare;
        if (sentiment > 400) return RarityTier.Rare;
        return RarityTier.Common;
    }
    
    /**
     * @dev Mint a new sentiment-based NFT
     * @param to Address to mint to
     * @param metadataURI Metadata URI for the NFT
     * @param attributes JSON string of NFT attributes
     */
    function mintNFT(
        address to,
        string memory metadataURI,
        string memory attributes
    ) external payable nonReentrant returns (uint256) {
        uint256 mintPrice = getCurrentMintPrice();
        require(msg.value >= mintPrice, "Insufficient payment");
        
        _tokenIds.increment();
        uint256 tokenId = _tokenIds.current();
        
        // Store NFT metadata
        nftMetadata[tokenId] = NFTMetadata({
            mintSentiment: currentSentiment,
            currentSentiment: currentSentiment,
            rarity: getRarityTier(currentSentiment),
            mintTimestamp: block.timestamp,
            attributes: attributes
        });
        
        _mint(to, tokenId);
        _setTokenURI(tokenId, metadataURI);
        
        emit NFTMinted(tokenId, to, currentSentiment, mintPrice);
        
        // Refund excess payment
        if (msg.value > mintPrice) {
            payable(msg.sender).transfer(msg.value - mintPrice);
        }
        
        return tokenId;
    }
    
    /**
     * @dev Update sentiment for all NFTs (internal)
     */
    function _updateAllNFTSentiments(uint256 newSentiment) internal {
        uint256 supply = _tokenIds.current();
        
        for (uint256 i = 1; i <= supply; i++) {
            if (_exists(i)) {
                NFTMetadata storage metadata = nftMetadata[i];
                metadata.currentSentiment = newSentiment;
                
                RarityTier newRarity = getRarityTier(newSentiment);
                if (newRarity != metadata.rarity) {
                    metadata.rarity = newRarity;
                    emit NFTEvolved(i, newSentiment, newRarity);
                }
            }
        }
    }
    
    /**
     * @dev Get NFT evolution data
     */
    function getNFTData(uint256 tokenId) external view returns (
        uint256 mintSentiment,
        uint256 currSentiment,
        RarityTier rarity,
        uint256 mintTimestamp,
        string memory attributes
    ) {
        require(_exists(tokenId), "Token does not exist");
        NFTMetadata memory metadata = nftMetadata[tokenId];
        return (
            metadata.mintSentiment,
            metadata.currentSentiment,
            metadata.rarity,
            metadata.mintTimestamp,
            metadata.attributes
        );
    }
    
    /**
     * @dev Get sentiment evolution for an NFT
     */
    function getSentimentEvolution(uint256 tokenId) external view returns (
        uint256 originalSentiment,
        uint256 currentSentimentValue,
        int256 sentimentChange
    ) {
        require(_exists(tokenId), "Token does not exist");
        NFTMetadata memory metadata = nftMetadata[tokenId];
        
        originalSentiment = metadata.mintSentiment;
        currentSentimentValue = metadata.currentSentiment;
        sentimentChange = int256(currentSentimentValue) - int256(originalSentiment);
        
        return (originalSentiment, currentSentimentValue, sentimentChange);
    }
    
    /**
     * @dev Withdraw contract funds (owner only)
     */
    function withdraw() external onlyOwner {
        uint256 balance = address(this).balance;
        require(balance > 0, "No funds to withdraw");
        payable(owner()).transfer(balance);
    }
    
    /**
     * @dev Get total number of minted NFTs
     */
    function totalSupply() external view returns (uint256) {
        return _tokenIds.current();
    }
    
    // Override required functions
    function _burn(uint256 tokenId) internal override(ERC721, ERC721URIStorage) {
        super._burn(tokenId);
    }
    
    function tokenURI(uint256 tokenId) public view override(ERC721, ERC721URIStorage) returns (string memory) {
        return super.tokenURI(tokenId);
    }
    
    function supportsInterface(bytes4 interfaceId) public view override(ERC721, ERC721URIStorage) returns (bool) {
        return super.supportsInterface(interfaceId);
    }
}