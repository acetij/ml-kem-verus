/*ntt.rs*/
use crate::arith::*;
use crate::poly::*;
use vstd::prelude::*; 

verus! {

//look-up table of pre-computed values for zeta^{bitrev(k)} (mod Q)
//These come directly from the FIPS 203
const ZETAS: [u16; 128] = [1, 1729, 2580, 3289, 2642, 630, 1897, 848,
1062, 1919, 193, 797, 2786, 3260, 569, 1746, 296, 2447, 1339, 1476, 3046,
56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2878, 1974, 821, 289, 331, 3253,
1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915, 2319,
1435, 807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227,
910, 17, 2761, 583, 2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156,
3015, 3050, 1703, 1651, 2789, 1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388,
733, 2337, 268, 641, 1584, 2298, 2037, 3220, 375, 2549, 2090, 1645, 1063, 319, 2773,
757, 2099, 561, 2466, 2594, 2804, 1092, 403, 1026, 1143, 2150, 2775, 886, 1722, 1212,
1874, 1029, 2110, 2935, 885, 2154];

pub fn ntt(f: &Poly) -> Poly 
    requires is_poly_valid(f),
    ensures is_poly_valid(&result),
{
    let mut result = Poly {coeffs: f.coeffs};
    let mut k = 1usize;
    let mut len = 128usize;

    while len >= 2 {
        let mut start = 0usize;
        while start < 256 {
            let zeta = ZETAS[k];
            k += 1;

            let mut j = start;
            while j < start + len {
                let t = mult_mod_Q(zeta as u16, result.coeffs[j + len]);
                let a = result.coeffs[j];

                result.coeffs[j + len] = sub_mod_Q(a, t);
                result.coeffs[j] = add_mod_Q(a, t);

                j += 1;
            }
            start += 2 * len;
        }
        len >>= 1;
    }
    result
}
//Forward NTT, 7 layers of Cooley-Tukey butterfilies
//Input: Polynomial with coefficients in [0,Q)
//Output: NTT-domain polynomial

//Inverse NTT
//7 layers of Gentleman-Sand butterflies in
//reverse. Followed by multiplication of every
//coefficient by 3303 (128^{-1} (mod 3329)
//Output: Polynomial with coefficients in [0,Q)
pub fn intt(f: &Poly) -> (result: Poly)
    requires is_poly_valid(f),
    ensures is_poly_valid(&result)
{
    let mut result = Poly { coeffs: f.coeffs};
    let mut k: usize = 127;
    let mut len: usize = 2;

    while len <= 128
        invariant
            len >= 2,
            len <= 256,
            k < 128,
            is_poly_valid(f),
            forall |i: int| 0 <= i < 256 ==> result.coeffs[i] < Q as u16,
        decreases 128 - len,
    {
        let mut start: usize = 0;
        while start < 256
            invariant
                start <= 256,
                len >= 2,
                len <= 256,
                k < 128,
                forall |i: int| 0 <= i < 256 ==> result.coeffs[i] < Q as u16,
            decreases 256 - start,
        {
            let zeta = ZETAS[k] as u16;
            if k > 0 {k -= 1}

            let mut j: usize = start;
            while j < start + len
                invariant
                    j >= start,
                    j <= start + len,
                    start + len <= 256,
                    forall |i: int| 0 <= i < 256 ==> result.coeffs[i] < Q as u16,
                decreases start + len - j,
            {
                let t = result.coeffs[j];
                result.coeffs[j] = add_mod_Q(t, result.coeffs[j + len]);
                result.coeffs[j + len] = sub_mod_Q(result.coeffs[j + len], t);
                result.coeffs[j + len] = mult_mod_Q(zeta, result.coeffs[j + len]);
                j += 1;
            }
            start += 2 * len;
        }
        len <<= 1;
    }

    //Multiplication by 128^{-1} mod 3329 = 3303
    let mut i: usize = 0;
    while i < 256
        invariant
            i <= 256,
            forall |j: int| 0 <= j < i ==> result.coeffs[j] < Q as u16,
            forall |j: int| i <= j < 256 ==> result.coeffs[j] < Q as u16,
        decreases 256 - i,

    {
        result.coeffs[i] = mult_mod_Q(result.coeffs[i], 3303u16);
        i += 1;
    }
    
    result
}






#[cfg(test)]
mod tests {
    use super::*;

    //NTT of zero polynomial should be zero!
    #[test]
    fn test_ntt_zero() {
        let zero = poly_zero();
        let result = ntt(&zero);
        assert_eq!(result.coeffs, [0u16; N]);
    }

    //NTT output stays in the interval [0,Q)
    //NTT is linear (i.e NTT(a + b) == NTT(a) + NTT(b)
    
    //NTT on constant polynomial
    #[test]
    fn test_ntt_constant() {
        let mut f = poly_unit();
        let result = ntt(&f);
        for i in 0..256 {
            assert_eq!(result.coeffs[i], 1u16,
                "Expected 1 at index {}, got {}", i, result.coeffs[i]);
        }
    }

    



}//tests

}//verus!
