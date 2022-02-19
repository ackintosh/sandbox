## 参考

- [【2021年版】NFTを発行してほしいという問い合わせが多いので発行方法とサンプルコードを公開します - SaaS企業で働くPdMエンジニアのブログ https://www.blockchainengineer.tokyo/entry/2021-issue-nft-code]
- [Solidity Tutorial – How to Create NFTs with Hardhat https://www.freecodecamp.org/news/solidity-tutorial-hardhat-nfts/]
- OpenZeppelin https://github.com/OpenZeppelin/openzeppelin-contracts
  - ERC-721 https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC721/ERC721.sol

## コマンド

```bash
# 依存関係のインストール
# (@openzeppelin/contracts など)
$ npm install

# 仮想ノードの起動
$ npx hardhat node

# コントラクトのデプロイ
$ npx hardhat run scripts/deploy.js

```

-- 

# Basic Sample Hardhat Project

This project demonstrates a basic Hardhat use case. It comes with a sample contract, a test for that contract, a sample script that deploys that contract, and an example of a task implementation, which simply lists the available accounts.

Try running some of the following tasks:

```shell
npx hardhat accounts
npx hardhat compile
npx hardhat clean
npx hardhat test
npx hardhat node
node scripts/sample-script.js
npx hardhat help
```
