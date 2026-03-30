# A$^2$F: Enabling FHE-Based Smart Contracts over Additively Homomorphic Confidential Blockchains

This repository contains a Proof of Concept (PoC) implementation of the **A$^2$F: Enabling FHE-Based Smart Contracts over Additively Homomorphic Confidential Blockchains** protocol. The project demonstrates an efficient conversion between additive ciphertexts and fully homomorphic ciphertexts.



## Experimental Setup & Dependencies

To ensure **reproducibility**—a critical standard in cryptographic research—this project utilizes a **Remote Dependency Locking** strategy. The cryptographic backends are pinned to specific revisions of the [Sunscreen](https://www.google.com/search?q=https://github.com/sunscreen-privacy/sunscreen) ecosystem.

- **Language**: Rust (Edition 2021)
- **FHE Scheme**: BFV (Microsoft SEAL Backend via Sunscreen)
- **Security Level**: 128-bit (following HomomorphicEncryption.org standards)
- **Parameters**: 
  - $N=1024$  (`SealQ128_1024`)
  - $N=2048$  (`SealQ128_2048`)
  - $N=4096$ (`SealQ128_4096`)

**Note**: All internal crates (`seal_fhe`, `logproof`, etc.) are locked to a specific Git Commit Hash to prevent "code rot" and ensure that the PoC remains buildable regardless of upstream API changes.



## Getting Started

### 1. Clone the Repository

```
git clone https://github.com/wwwchenke/A2F.git
cd A2F
```

### 2. Build from Source and Run the PoC

Due to the computational intensity of FHE arithmetic (NTT, Barrett reduction, etc.), it is essential to compile in `release` mode to achieve expected performance:

```
cargo build
cargo run --release
```