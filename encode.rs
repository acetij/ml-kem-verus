/*encode.rs*/

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

#[cfg(test)]
mod tests {
    use super::*;
}

