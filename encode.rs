/*encode.rs*/
use crate::poly::*;
use crate::arith::*;
use::vstd::prelude::*;

verus! {


/***SPEC FUNCTIONS***/
pub open spec fn valid_d_coeff(x: u16, d: u32) -> bool {
    x < pow2(d as nat)
}

pub open spec fn encode_valid(d: u32, len: usize) -> bool {
    len == 32 * d
}


//ByteEncode output validity
pub open spec fn byte_encode_valid(encoded: &[u8], d: u32) -> bool {
    encoded.len() == 32 * d as usize
}

//Mathematical description of compress and how it should function.
pub open spec fn spec_compress(x: u16, d: u32) -> u16 {
    ((x as int * pow2(d as nat) as int + Q as int / 2)
     / Q as int % pow2(d as nat) as int) as u16
}

//Mathematical description of decompress and how it should functoin.
pub open spec fn spec_decompress(y: u16, d: u32) -> u16 {
    ((y as int * Q as int * pow2(d as nat) as int / 2)
     / pow2(d as nat) as int) as u16
}

//The compress/decompress error bound from FIPS203
pub open spec fn compress_error_bound(d: u32) -> int {
    //round(q / 2^(d+1))
    (Q as int + pow2((d + 1) as nat) as int / 2)
        / pow2((d + 1) as nat) as int
}

//ByteEncode output validity
pub open spec fn byte_encode_valid(encoded: &[u8], d: u32) -> bool {
    encoded.len() == 32 * d as usize
}

//Roundtrip property for ByteEncode/ByteDecode
//Here we verify that: 
pub open spec fn spec_encode_decode_roundtrip(f: &Poly, d: u32) -> bool {
    forall |i: int| 0 <= i < 256 ==>
        spec_byte_decode(spec_byte_encode(f, d), d).coeffs[i] == f.coeffs[i]
}

//Compress output is in valid range
pub open spec fn compress_output_valid(x: u16, d: u32) -> bool {
    spec_compress(x,d) < pow2(d as nat) as u16
}


/***PROOFS***/

// Compress output is always in [0, 2^d)
proof fn lemma_compress_output_valid(x: u16, d: u32)
    requires
        x < Q as u16,
        1 <= d <= 12,
    ensures
        spec_compress(x,d) < pow2(d as nat) as u16,
{}

//Decompress output is always in range [0,Q)
proof fn lemma_decompress_output_valid(y: u16, d: u32)
    requires
        y < pow2(d as nat) as u16,
        1 <= d <= 12,
    ensures
        spec_decompress(y, d) < Q as u16,
{}

/*
 * Note: This still needs to be worked out
//The error bound
//|Decompress(Compress(x)) - x | (mod Q) <= round(Q / 2^(d+1))
proof fn lemma_compress_decompress_error_bound(x: u16, d: u32)
    requires
        x < Q as u16,
        1 <= d <= 12,
    ensures ({
        let compressed = spec_compress(x,d);
        let decompressed = spec_decompress(compressed, d);
        let diff = if decompressed >= x {
            decompressed - x
        } else {
            x - decompressed
        };
        diff <= compress_error_bound(d) as u16
    }),

{
    //will need nonlinear arithmetic hints
    //Consider external_body to start
}
*/


//Compress is deterministic
proof fn lemma_compress_deterministic(x: u16, d: u32)
    requires
        x < Q as u16,
        1 <= d <= 12,
    ensures
        spec_compress(x,d) == spec_compress(x,d),
{}



/*-ByteEncode/ByteDcode proofs-*/
proof fn lemma_byte_decode_12_coeff_range(bytes: &[u8; 384]) 
    ensures
        forall |i: int| 0 <= i < 256 ==>
            byte_decode_12(bytes).coeffs[i] < (1u16 << 12)
{}

proof fn lemma_byte_decode_10_coeff_range(bytes: &[u8; 320])
    ensures
        forall |i: int| 0 <= i < 256 ==>
            byte_decode_10(bytes).coeffs[i] < (1u16 << 10),
{}

proof fn lemma_byte_decode_4_coeff_range(bytes: &[u8; 128])
    ensures
        forall |i: int| 0 <= i < 256 ==>
            byte_decode_4(bytes).coeffs[i] < (1u16 << 4)
{}

proof fn lemma_byte_decode_1_coeff_range(bytes: &[u8; 32])
    ensures
        forall |i: int| 0 <= i < 256 ==>
            byte_decode_1(bytes).coeffs[i] < 2u16,
{}


//This is probably the most important proof we want to esbtablish
//in encode.rs. That is, ByteDecode(ByteEncode(f)) = f
//We will start with d = 12 since it's the most important.

#[verifier::external_body]
proof fn lemma_byte_encode_decode_12_roundtrip(f: &Poly)
    requires
        forall |i: int| 0 <= i < 256 ==>
            f.coeffs[i] < (1u16 << 12),
    ensures
        forall |i: int| 0 <= i < 256 ==>
            byte_decode_12(&byte_encode_12(f)).coeffs[i] == f.coeffs[i]
{}

/***EXECUTABLE FUNCTIONS***/
/*Bits To Bytes*/
//Input: bit array b \in {0,1}^{8*l}
//Output: byte array B \in \mathbb{B}^{l}

pub fn bits_to_bytes(bits: &[u8], out: &mut [u8]) {
    debug_assert_eq!(bits.len(), out.len() * 8);
    for i in 0..bits.len() {
        out[i / 8] |= bits[i] << (i % 8);
    }
}


pub fn bytes_to_bits(bytes: &[u8], out: &mut [u8]) {
    debug_assert_eq!(out.len(), bytes.len() * 8);
    for i in 0..out.len() {
        out[i] = (bytes[i / 8] >> (i % 8)) & 1;
    }
}


pub fn byte_encode_12(f: &Poly) -> [u8; 384] {
    //Step 1 is to extract 12 bits from each coefficient
    let mut bits = [0u8; 3072]; //256 * 12 bits
    for i in 0..256 {
        let coeff = f.coeffs[i];
        for j in 0..12 {
            bits[i * 12 + j] = ((coeff >> j) & 1) as u8;
        }
    }
    //Step 2 pack bits into bytes using our function.
    let mut result = [0u8; 384];
    bits_to_bytes(&bits, &mut result);
    result
}

pub fn byte_decode_12(bytes: &[u8; 384]) -> Poly {
    //Step 1 - unpack bytes into bits using our function
    let mut bits = [0u8; 3072];
    bytes_to_bits(bytes, &mut bits);
    //Step 2 - reconstruct coefficients from 12 bits each
    let mut result = poly_zero();
    for i in 0..256 {
        let mut coeff = 0u16;
        for j in 0..12 {
            coeff |= (bits[i * 12 + j] as u16) << j;
        }
        result.coeffs[i] = coeff;
    }
    result
}

pub fn byte_encode_10(f: &Poly) -> [u8; 320] {
    //Extract 10 bits from each coefficient
    let mut bits = [0u8; 2560];
    for i in 0..256 {
        for j in 0..10 {
            bits[i * 10 + j] = ((f.coeffs[i] >> j) & 1) as u8;
        }
    }
    //Pack bits into bytes
    let mut result = [0u8; 320];
    bits_to_bytes(&bits, &mut result);
    result
}


pub fn byte_decode_10(bytes: &[u8; 320]) -> Poly {
    //unpack given bytes into bits
    let mut bits = [0u8; 2560];
    bytes_to_bits(bytes, &mut bits);
    //reconstruct coefficients from 10bits each
    let mut result = poly_zero();
    for i in 0..256 {
        let mut coeff = 0u16;
        for j in 0..10 {
            coeff |= (bits[i * 10 + j] as u16) << j;
        }
        result.coeffs[i] = coeff;
    }
    result
}


pub fn byte_encode_4(f: &Poly) -> [u8; 128] {
    //Extract 4 bits from each coefficient
    let mut bits = [0u8; 1024];
    //Reconstruct coefficients from 4 bits each
    for i in 0..256 {
        for j in 0..4 {
            bits[i * 4 + j] = ((f.coeffs[i] >> j) & 1) as u8;
        }
    }
    //pack bits into bytes
    let mut result = [0u8; 128];
    bits_to_bytes(&bits, &mut result);
    result
}


pub fn byte_decode_4(bytes: &[u8; 128]) -> Poly {
    //unpack given bytes into bits
    let mut bits = [0u8; 1024];
    bytes_to_bits(bytes, &mut bits);
    //reconstruct coefficients from 10bits each
    let mut result = poly_zero();
    for i in 0..256 {
        let mut coeff = 0u16;
        for j in 0..4 {
            coeff |= (bits[i * 4 + j] as u16) << j;
        }
        result.coeffs[i] = coeff;
    }
    result
}


pub fn byte_encode_1(f: &Poly) -> [u8; 32] {
    //Extract 1 bit from each coefficient
    let mut bits = [0u8; 256];
    //Reconstruct coefficients from 1 bit each
    for i in 0..256 {
        bits[i] = (f.coeffs[i] & 1) as u8;
    }
    //pack bits into bytes
    let mut result = [0u8; 32];
    bits_to_bytes(&bits, &mut result);
    result
}


pub fn byte_decode_1(bytes: &[u8; 32]) -> Poly {
    //unpack given bytes to bits
    let mut bits = [0u8; 256];
    bytes_to_bits(bytes, &mut bits);
    //reconstruct coefficients from 1 bit each
    let mut result = poly_zero();
    for i in 0..256 {
        let mut coeff = 0u16;
        for j in 0..1 {
            coeff |= (bits[i + j] as u16) << j;
        }
        result.coeffs[i] = coeff;
    }
    result
}


//Compress/Decompress
/*Recall that q = 3329, and that the bit length of q is 12. For d < 12,
 * define,
 *
 * Compress_d: Z/qZ --> Z/2^dZ; x |-> [(2^d/q) * x] (mod 2^d)
 * Decompress_d: Z/2^dZ --> Z/qZ; y |-> [q/2^d * y]
 *
 *
 * pub fn compress(x: u16, d: u32) -> u16 {}
 * pub fn decompress(x: u16, d: u32) -> u16 {}
 * 
 * pub fn poly_compress(f: &Poly, d: u32) -> Poly {}
 * pub fn poly_decompress(f: &Poly, d: u32) -> Poly {}
 *
 */

pub fn compress(x: u16, d: u32) -> u16 {
    let numerator = (x as u64) * (1u64 << d) + (Q as u64 / 2);
    let divided = numerator / Q as u64; //divide by q-not a shift
    (divided & ((1u64 << d) - 1)) as u16
}

pub fn decompress(y: u16, d: u32) -> u16 {
    let numerator = (y as u64) * Q as u64 + (1u64 << (d - 1));
    (numerator >> d) as u16
}


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_byte_encode_decode_12_roundtrip() {
        let f = Poly {
            coeffs: core::array::from_fn (|i| (i as u16 * 7) % Q as u16)
        };
        let encoded = byte_encode_12(&f);
        let decoded = byte_decode_12(&encoded);
        assert_eq!(decoded.coeffs, f.coeffs);
    }

    #[test]
    fn test_byte_encode_decode_10_roundtrip() {
        let f = Poly {
            coeffs: core::array::from_fn(|i| (i as u16 * 5) % 1024u16)
        };
        let encoded = byte_encode_10(&f);
        let decoded = byte_decode_10(&encoded);
        assert_eq!(decoded.coeffs, f.coeffs);
    }

    #[test]
    fn test_byte_encode_decode_4_roundtrip() {
        let f = Poly {
            coeffs: core::array::from_fn(|i| (i as u16 * 3) % 16u16)
        };
        let encoded = byte_encode_4(&f);
        let decoded = byte_decode_4(&encoded);
        assert_eq!(decoded.coeffs, f.coeffs);
    }

    #[test]
    fn test_byte_encode_decode_1_roundtrip() {
        let f = Poly {
            coeffs: core::array::from_fn(|i| (i as u16) % 2u16)
        };
        let encoded = byte_encode_1(&f);
        let decoded = byte_decode_1(&encoded);
        assert_eq!(decoded.coeffs, f.coeffs);
    }

    #[test]
    fn test_byte_encode_decode_12_zero() {
        let zero = poly_zero();
        let encoded = byte_encode_12(&zero);
        let decoded = byte_decode_12(&encoded);
        assert_eq!(decoded.coeffs, [0u16; 256]);
    }

    //Output side testing

    #[test]
    fn test_byte_encode_12_output_size() {
        let f = Poly {coeffs: [1u16; 256]};
        let encoded = byte_encode_12(&f);
        //256 * 12/8
        assert_eq!(encoded.len(), 384);
    }

    #[test]
    fn test_byte_encode_10_output_size() {
        let f = Poly {coeffs: [1u16; 256] };
        let encoded = byte_encode_10(&f);
        assert_eq!(encoded.len(), 320); //256 * 10/8
    }

    #[test]
    fn test_byte_encode_4_output_size() {
        let f = Poly {coeffs: [1u16; 256] };
        let encoded = byte_encode_4(&f);
        //256 * 4/8
        assert_eq!(encoded.len(), 128);
    }

    #[test]
    fn test_byte_encode_1_output_size() {
        let f = Poly {coeffs: [1u16; 256] };
        let encoded = byte_encode_1(&f);
        //256 * 1/8
        assert_eq!(encoded.len(), 32);
    }

    
    //Coeffiicnet range testing

    #[test]
    fn test_byte_decode_12_coeff_range() {
        let bytes = [0xFFu8; 384];
        let decoded = byte_decode_12(&bytes);
        for i in 0..256 {
            assert!(decoded.coeffs[i] < (1 << 12),
            "coefficient {} out of 12-bit range at index {}",
            decoded.coeffs[i], i);
        }
    }

    #[test]
    fn test_byte_decode_10_coeff_range() {
        let bytes = [0xFFu8; 320];
        let decoded = byte_decode_10(&bytes);
        for i in 0..256 {
            assert!(decoded.coeffs[i] < (1 << 10),
            "coefficient {} out of 10-bit range at index {}",
            decoded.coeffs[i],i);
        }
    }

    #[test]
    fn test_byte_decode_4_coeff_range() {
        let bytes = [0xFFu8; 128];
        let decoded = byte_decode_4(&bytes);
        for i in 0..256 {
            assert!(decoded.coeffs[i] < (1 << 4),
            "coefficient {} out of 4-bit range at index {}",
            decoded.coeffs[i], i);
        }
    }

    #[test]
    fn test_byte_decode_1_coeff_range() {
        let bytes = [0xFFu8; 32];
        let decoded = byte_decode_1(&bytes);
        for i in 0..256 {
            assert!(decoded.coeffs[i] < (1 << 1),
            "coefficient {} out of 1-bit range at index {}",
            decoded.coeffs[i], i);
        }
    }



    

}//test

}//verus!

