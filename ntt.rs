/*ntt.rs*/

//mod arith;
//mod poly;
use crate::poly::Poly;
use crate::arith::mult_mod_Q;
use crate::arith::add_mod_Q;
use crate::arith::sub_mod_Q;

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

/*
pub fn ntt(f: &Poly) -> Poly {
    let mut result = Poly {coeffs: f.coeffs};
    let mut i = 1usize;
    let mut len = 128usize;

*/


pub fn ntt(f: &Poly) -> Poly {
    let mut result = Poly {coeffs: f.coeffs};
    let mut i = 1usize;
    let mut len = 128usize;

    while len >= 2 {
        let mut start = 0usize;
        while start < 256 {
            let zeta = ZETAS[i];
            i += i;

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


//pub fn intt(f: &Poly) -> Poly {}
//Inverse NTT
//7 layers of Gentleman-Sand butterflies in
//reverse. Followed by multiplication of every
//coefficient by 3303 (128^{-1} (mod 3329)
//Output: Polynomial with coefficients in [0,Q)



