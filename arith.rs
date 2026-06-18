/*/src/arth.rs
 * TODO 
 * 1. Functionally verify modular addition, subtraction, multiplication (Verus)
 */

use vstd::prelude::*;

verus! {

//Implementations///
///////////////////
pub const Q: u32 = 3329;

pub fn reduce_mod_Q(r: u32) -> u16 {
    (r % Q) as u16
}

pub fn add_mod_Q(r: u16, s: u16) -> u16 {
    reduce_mod_Q(r as u32 + s as u32)
}

pub fn sub_mod_Q(r: u16, s:u16) -> u16 {
    reduce_mod_Q(r as u32 + Q - s as u32)
}

pub fn mult_mod_Q(r: u16, s:u16) -> u16 {
    reduce_mod_Q(r as u32 * s as u32)
}

//Spec Functions//
/////////////////

pub open spec fn valid_coeff(r: u16) -> bool {
    r < Q as u16
}

pub open spec fn valid_coeff_u32(r: u32) -> bool {
    r < Q
}



// *** Proof Lemmas ***

mod lemmas {
    use super::*;

    pub proof fn lemma_add_identity(r: u16)
        requires valid_coeff(r),
        ensures add_mod_Q(r, 0) == r,
    {}

    pub proof fn lemma_add_commutative(r: u16, s: u16)
        requires valid_coeff(r), valid_coeff(s),
        ensures add_mod_Q(r, s) == add_mod_Q(s, r),
    {}

    pub proof fn lemma_add_associative(r: u16, s: u16, t: u16)
        requires valid_coeff(r), valid_coeff(s), valid_coeff(t),
        ensures add_mod_Q(r, add_mod_Q(s, t)) == add_mod_Q(add_mod_Q(r,s),t),
    {}

    pub proof fn lemma_add_closed(r: u16, s: u16)
        requires valid_coeff(r), valid_coeff(s),
        ensures valid_coeff(add_mod_Q(r, s)),
    {}

    pub proof fn lemma_add_sub_inverse(r: u16, s: u16)
        requires valid_coeff(r), valid_coeff(s),
        ensures sub_mod_Q(add_mod_Q(r, s),s) == r,
    {}

    pub proof fn lemma_mult_commutative(r: u16, s: u16)
        requires valid_coeff(r), valid_coeff(s),
        ensures 

}

/*
 * TEST FUNCTIONS
 */
#[cfg(test)]
    //only used for matrix_ntt
    pub fn mod_pow(mut base: u32, mut exp: u32, modulus: u32) -> u32 {
        let mut result = 1u32;
        base %= modulus;
        while exp > 0 {
            if exp & 1 == 1 {
                result = (result as u64 * base as u64 % modulus as u64) as u32;
            }
            exp >>= 1;
            base = (base as u64 * base as u64 % modulus as u64) as u32;
        }
        result
    }
    mod tests {
        use super::*;

        #[test]
        fn reduce_Q() {
            let result = reduce_mod_Q(3330);
            assert_eq!(result,1);
        }

        #[test]
        fn reduce_add_Q() {
            let result = add_mod_Q(3328,1);
            assert_eq!(result, 0);
        }

        #[test]
        fn test_add_identity() {
            let r = 1337u16;
            assert_eq!(add_mod_Q(r,0), r);
            assert_eq!(add_mod_Q(0,r), r);
        }

        #[test]
        fn test_add_commutative() {
            let r = 1234u16;
            let s = 5678u16 % 3329;
            assert_eq!(add_mod_Q(r,s), add_mod_Q(s,r));
        }

        #[test]
        fn test_add_associative() {
            let r = 100u16;
            let s = 200u16;
            let t = 300u16;
            assert_eq!(
                add_mod_Q(r,add_mod_Q(s,t)),
                add_mod_Q(add_mod_Q(r,s),t))
        }


        #[test]
        fn reduce_sub_Q() {
            let result = sub_mod_Q(3329,3329);
            assert_eq!(result, 0);
        }

        #[test]
        fn reduce_add_Q_wraps() {
            let result = add_mod_Q(3328,1);
            assert_eq!(result, 0);
        }

        #[test]
        fn reduce_sub_Q_wraps() {
            let result = sub_mod_Q(0,1);
            assert_eq!(result, 3328);
        }

        #[test]
        fn reduce_mult_Q() {
            let result = mult_mod_Q(3328,3328);
            assert_eq!(result,1);
        }
    }
}//verus!

