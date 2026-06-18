/*arith.rs*/
use vstd::prelude::*;

verus! {

pub const Q: u32 = 3329;

/*SPEC FUNCTIONS*/
pub open spec fn is_valid_coeff(r: u16) -> bool {
    r < Q as u16
}

pub open spec fn is_valid_coeff_u32(r: u32) -> bool {
    r < Q
}

pub open spec fn spec_add_mod_Q(r: u16, s: u16) -> u16 {
    ((r as int + s as int) % Q as int) as u16
}

pub open spec fn spec_sub_mod_Q(r: u16, s: u16) -> u16 {
    ((r as int + Q as int - s as int) % Q as int) as u16
}

pub open spec fn spec_mult_mod_Q(r: u16, s: u16) -> u16 {
    ((r as int * s as int) % Q as int) as u16
}

//Executable (modular reduction)
pub fn reduce_mod_Q(r: u32) -> (result: u16)
    ensures
        result == (r % Q) as u16,
        is_valid_coeff(result),
{
    (r % Q) as u16
}

//Executable (modular addition)
pub fn add_mod_Q(r: u16, s: u16) -> (result: u16)
    requires
        is_valid_coeff(r),
        is_valid_coeff(s),
    ensures
        result == spec_add_mod_Q(r,s),
        is_valid_coeff(result),
{
    reduce_mod_Q(r as u32 + s as u32)
}

//Executable (modular subtraction)
pub fn sub_mod_Q(r: u16, s: u16) -> (result: u16)
        requires
            is_valid_coeff(r),
            is_valid_coeff(s),
        ensures
            result == spec_sub_mod_Q(r,s),
            is_valid_coeff(result),

{
    reduce_mod_Q(r as u32 + Q - s as u32)
}

#[verifier::external_body]
pub fn mult_mod_Q(r: u16, s: u16) -> u16 {
    reduce_mod_Q(r as u32 * s as u32)
}

/*PROOFS*/
proof fn lemma_add_closure(r: u16, s: u16)
    requires
        is_valid_coeff(r),
        is_valid_coeff(s),
    ensures
        is_valid_coeff(spec_add_mod_Q(r,s)),
{}


proof fn lemma_add_identity(r: u16) 
    requires is_valid_coeff(r),
    ensures
        spec_add_mod_Q(r,0) == r,
        spec_add_mod_Q(0,r) == r,
{}

proof fn lemma_add_commutative(r: u16, s: u16)
    requires
        is_valid_coeff(r),
        is_valid_coeff(s),
        ensures
            spec_add_mod_Q(r,s) == spec_add_mod_Q(s,r),
{}

proof fn lemma_add_assoc(r: u16, s: u16, t: u16)
    requires
        is_valid_coeff(r),
        is_valid_coeff(s),
        is_valid_coeff(t),
    ensures
        spec_add_mod_Q(spec_add_mod_Q(r,s), t) == spec_add_mod_Q(r, spec_add_mod_Q(s,t)),
{}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduce_Q() {
        let result = reduce_mod_Q(3330);
        assert_eq!(result, 1);
    }

    #[test]
    fn reduce_add_Q() {
        let result = add_mod_Q(3328, 1);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_add_identity() {
        let r = 1337u16;
        assert_eq!(add_mod_Q(r,0),r);
        assert_eq!(add_mod_Q(0,r),r);
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
            add_mod_Q(r, add_mod_Q(s,t)),
            add_mod_Q(add_mod_Q(r,s),t));
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
        let result = mult_mod_Q(3328, 3328);
        assert_eq!(result, 1);
    }

}//tests

}//verus!



