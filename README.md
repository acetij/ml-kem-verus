# ml-kem-verus
Formally verified ML-KEM-768 (CRYSTALS-Kyber) implementation in Rust using Verus. Proving functional correctness of modular arithmetic, polynomial operations, and NTT.

## What is this?

ML-KEM (formerly CRYSTALS-Kyber) is a post-qunatumm key encapsulation method which was standarized by NIST in FIPS 203 (2024). The objective of this project is to implement ML-KEM-768 in Rust with formal correctness proofs utilizing Verus.

## What is verified?

- `arith.rs` — Modular arithmetic over $\mathbb{Z} /(q = 3329) \mathbb{Z}$
  - Coefficient bounds preserved through add, sub, mul
  - Algebraic properties: commutativity, associativity, identity
  - Addition/subtraction inverse relationship

- `poly.rs` — Polynomial operations in $(\mathbb{Z}/(q = 3329) \mathbb{Z})[X] / (X^{256} + 1)$
  - Coefficient validity preserved through poly_add, poly_sub
  - Polynomial algebraic properties
 
  ## What Is Not Yet Verified

- NTT correctness (in progress)
- ByteEncode/ByteDecode roundtrip
- Compress/Decompress error bounds
- End-to-end functional correctness of KeyGen/Encaps/Decaps


## Mathematical Background
### Module-LWE

### Polynomial Ring and Polynomial Arithmetic
ML-KEM-768 makes use of the polynomial quotient ring 

$$R_q = \frac{\mathbb{Z} / 3329 \mathbb{Z}[X]}{x^{256} + 1}$$

Then give $f$ as an element of $R_q$ we see that in general it will have the form:

$$f(X) = a_0 + a_1X + a_2X^2 + \dots + a_{256}X^{256}, \hspace{5mm} a_j \in \frac{Z}{3329 \mathbb{Z}}$$

polynomial addition is the usual polynomial addition but taken modulo $3329$.

polynomial multiplication is the usual polynomial multiplication followed by a reduction $X^{256} \equiv -1 ( \mod 3329 )$.

### Number Theoretic Transform

The Number Theoretic Transform (NTT) is at the heart of the ml-kem scheme. Speaking purely mathematically, one can understand NTT as a ring-isomorphism. Recall for ml-kem-768 (FIPS 203) we use the fixed modulus $q = 3329$ and ring dimension $n = 256$. There exist $128$ primitive $256$-th roots of unity and no primitive $512$-th root of unity in $\mathbb{Z} / q \mathbb{Z}$. Further, we use the primitive-root $\zeta = 17 \in \mathbb{Z} / q \mathbb{Z}$. There also exists a function which isn't directly implemented in this project (nor too the standards of FIPS 203) which is $\operator{Bitrev}_7(i)$.

One can observe that the polynomial $X^{256} + 1$ can be factored in the following manner:

$$X^{256} + 1 = \prod_{i=0}^{127} (X^2 - \zeta^{2 Bitrev_7(i) + 1})$$

In turn, it follows that $R_q \cong (\mathbb{Z}/q\mathbb{Z})[X]/(X^{256} + 1)$ is isomorphic to the direct sum of $128$ quadratic extension fields $\mathbb{Z}/q\mathbb{Z}$, which in the literature is to be denoted $T_q$. That is, $T_q$ has the following structure:

$$T_q \equiv \bigoplus_{i=0}^{127} \mathbb{Z}/q\mathbb{Z}/(X^2 - \zeta^{2 Bitrev_7(i) + 1}).$$

More explicitly, the NTT form of a given polynomial $f \in R_q$ which we will denote $\hat{f} \in T_q$ can be realized as the vector which consists of the corresponding residues of degree at most one. So that we have:

$$\hat{f} \equiv (f \mod ((X^2 - \zeta^{2 Bitrev_7(i) + 1})), \dots, f \mod (X^2 - \zeta^{2 Bitrev_7(i) + 1}))$$


## Formal Verification

arith.rs:

## Modular Reduction
reduce_mod_Q(r: u16, s: u16) -> (result: u16) 

**What does it do?**:  Given an integer $r$, it reduces $r (mod Q)$.

### Verified properties




### Modular Addition
add_mod_Q(r: u16, s: u16) -> (result: u16)  

### Modular Subtraction
sub_mod_Q(r: u16, s: u16) -> (result: u16)  

### Modular Multiplication
mult_mod_Q(r: u16, s: u16) -> (result: u16)  


poly.rs

poly_zero() -> Poly
poly_unit() -> Poly

poly_add_Q(r: &Poly, s: &Poly) -> (result: Poly)




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
encode.rs - encoding/decoding (in progress)
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
