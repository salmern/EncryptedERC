<div align="center">
  <img src="images/banner.png">
</div>

---

# Encrypted ERC-20 Protocol

The Encrypted ERC-20 (eERC) standard enables secure and confidential token transfers on Avalanche blockchains. Leveraging zk-SNARKs and partially homomorphic encryption, the eERC protocol offers robust privacy without requiring protocol-level modifications or off-chain intermediaries.

## Key features

- Confidential Transactions: User balances and transaction amounts remain completely hidden, ensuring financial privacy.
- Large Integers: Efficiently handles token amounts up to 128 bits (2^128), accommodating substantial financial transactions.
- Client-Side Operations: Users retain control, performing encryption, decryption, and zk-proof generation directly on their own devices.
- Fully On-chain Nature: Operates entirely on-chain without the need for relayers or off-chain actors.
- Built-in Compliance: Supports external auditors, ensuring regulatory compliance.

## File structure

- [contracts](#contracts) Smart contract source files
- [scripts](#scripts) Utility and deployment scripts
- [src](#src) Encryption utilities for TypeScript
- [tests](#tests) Test scripts and helpers
- [zk](#zk) Gnark-based implementations of zero-knowledge proof components

## Getting Started

### Prerequisites

You need following dependencies for setup:

- `NodeJS >= v16.x `
- `Golang >= 1.23.x `

### Installation

1. Clone the repo
   ```sh
   git clone https://github.com/ava-labs/EncryptedERC.git
   ```
2. Install NPM packages

   ```sh
   npm install
   ```

   Note: This command will run a bash script to compile gnark's circuits, if this does not work:
   In [zk](#zk) directory run the following command to build manually:

   On arm64:

   ```sh
   go build -o ../outputs/eerc20_zk
   ```

### Run Tests/Coverage

Contract tests:

```
npx hardhat coverage
```

## 📊 Performance Overview

### ⛽ Avg. On-Chain Gas Costs (C-Chain Mainnet)

| **Operation**    | **Gas Cost**  |
| ---------------- | ------------- |
| Register         | 315,972 gas   |
| Deposit          | _TODO_        |
| Withdraw         | _TODO_        |
| Private Burn     | 872,351 gas   |
| Private Mint     | 704,179 gas   |
| Private Transfer | 929,429 gas   |
| Update Auditor   | 103,800 gas   |

### ⏱️ Circuit Benchmarks for Proof Generation

Tested on M3 Pro CPU:

| **Operation**    | **Proving Time** |
| ---------------- | ---------------- |
| Registration     | 71 ms            |
| Private Mint     | 359 ms           |
| Private Burn     | 360 ms           |
| Private Transfer | 606 ms           |
