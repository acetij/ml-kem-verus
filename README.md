# ml-kem-verus
Formally verified ML-KEM-768 (CRYSTALS-Kyber) implementation in Rust using Verus. Proving functional correctness of modular arithmetic, polynomial operations, and NTT.

## What is this?

ML-KEM (formerly CRYSTALS-Kyber) is a post-qunatumm key encapsulation method which was standarized by NIST in FIPS 203 (2024). The objective of this project is to implmemnt ML-KEM-768 in Rust with formal correctness proofs utilizing Verus

## What is verified?

- `arith.rs` — Modular arithmetic over Z_q (q = 3329)
  - Coefficient bounds preserved through add, sub, mul
  - Algebraic properties: commutativity, associativity, identity
  - Addition/subtraction inverse relationship

- `poly.rs` — Polynomial operations in (Z/qZ)[x]/(x^256 + 1)
  - Coefficient validity preserved through poly_add, poly_sub
  - Polynomial algebraic properties
 
  ## What Is Not Yet Verified

- NTT correctness (in progress)
- ByteEncode/ByteDecode roundtrip
- Compress/Decompress error bounds
- End-to-end functional correctness of KeyGen/Encaps/Decaps

## Important Note on Security

These proofs establish **functional correctness**, not cryptographic security.
IND-CCA2 security of ML-KEM follows from the NIST standardization process
and existing proofs in the literature. This project does not claim or prove
cryptographic security properties.

## Running the Code

### Prerequisites
- Rust (stable)
- Verus (see [installation](https://github.com/verus-lang/verus/blob/main/INSTALL.md))


### Run tests
```bash
cargo test
```

### Run Verus verification
```bash
verus src/lib.rs --crate-type lib
```
## Project Structure

/src
lib.rs - module declerations
arith.rs - verified modular arithmetic
poly.rs - verified polynomial arithmetic
ntt.rs - NTT/INTT (in progress)
encode.rs - encoding/decoding (planned)
sample.rs - sampling (planned)
hash.rs - hash functions (planned)
matrix.rs - module operations (planned)
kem.rs - KeyGen, Encaps, Decaps (planned)


## References

- [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final) — ML-KEM Standard
- [Verus](https://github.com/verus-lang/verus) — Verification framework
- [CRYSTALS-Kyber](https://pq-crystals.org/kyber/) — Original submission

## Status

Work in progress. Arithmetic and polynomial layers are substantially complete
with Verus proofs. NTT verification is the current focus.
