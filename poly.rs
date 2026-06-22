/*poly.rs*/
use vstd::prelude::*;
//use crate::arith::*;
use crate::arith::add_mod_Q;
use crate::arith::sub_mod_Q;
use crate::arith::Q;
use crate::arith::is_valid_coeff;

verus! {

pub const N: usize = 256;

pub struct Poly {
    pub coeffs: [u16;N],
}

/* SPEC FUNCTIONS*/
/*
pub open spec fn is_valid_coeff(p: &Poly) -> bool {
    forall |i: int| 0 <= i < N as int ==> p.coeffs[i as int] < Q as u16
}
*/

pub open spec fn is_poly_valid(p: &Poly) -> bool {
    forall |i: int| 0 <= i < N as int ==> p.coeffs[i] < Q as u16
}

/*
pub open spec fn spec_poly_add(p: &Poly, q: &Poly) -> Poly {
    Poly {
        coeffs: Seq::new(N as nat, |i: nat|
                    (p.coeffs[i as usize] + b.coeffs[i as usize]) % Q as u16
        )
    }
}
*/

//Two polynomials are equivalent
pub open spec fn poly_eq(p: &Poly, q: &Poly) -> bool {
    forall |i: int| 0 <= i < N as int ==> p.coeffs[i] == q.coeffs[i]
}

pub open spec fn spec_poly_zero() -> Poly {
    Poly {coeffs: [0u16; N]}
}


/*EXECUTABLE FUNCTIONS*/
//constructor for the zero polynomial.
pub fn poly_zero() -> Poly {
    Poly {coeffs: [0u16; N]}
}

//constructor for the unit polynomial.
pub fn poly_unit() -> Poly {
    Poly {coeffs: [1u16; N]}
}


pub fn poly_add_Q(r: &Poly, s: &Poly) -> (result: Poly)
    requires
        is_poly_valid(r),
        is_poly_valid(s),
    ensures
        is_poly_valid(&result),
{
    let mut result = poly_zero();
    let mut i = 0usize;
    while i < N
        invariant
            i <= N,
            is_poly_valid(r),
            is_poly_valid(s),
            forall |j: int| 0 <= j < i ==> result.coeffs[j] < Q as u16,
        decreases
            N - i,
    {
    assert(is_valid_coeff(r.coeffs[i as int])) by {
        assert(is_poly_valid(r));
    }
    assert(is_valid_coeff(s.coeffs[i as int])) by {
        assert(is_poly_valid(s));
    }
        result.coeffs[i] = add_mod_Q(r.coeffs[i], s.coeffs[i]);
        i += 1;
    }
    result
}



/*
pub fn poly_sub_Q(r: &Poly, s: &Poly) -> Poly {
    let mut result = poly_zero();
    for i in 0..N {
        result.coeffs[i] = sub_mod_Q(r.coeffs[i], s.coeffs[i]);
    }
    result
}
*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_poly_add_zero() {
        let p = Poly {coeffs: [1u16; N]};
        let zero = poly_zero();
        let result = poly_add_Q(&p, &zero);
        assert_eq!(result.coeffs, p.coeffs);
    }

    #[test]
    fn test_poly_sub_self() {
        let p = Poly {coeffs: [100u16; N]};
        let result = poly_sub_Q(&p, &p);
        assert_eq!(result.coeffs, [0u16; N]);
    }
    
    #[test]
    fn test_polynomial_add_Q_bounds() {
        let p = Poly {coeffs: [3328u16; N]};
        let q = Poly {coeffs: [3328u16; N]};
        let result = poly_add_Q(&p, &q);
        for i in 0..N {
            assert!(result.coeffs[i] < 3329,
                "coefficient {} out of bounds at index {}",
                result.coeffs[i],i);
        }
    }
    
    #[test]
    fn test_poly_add_wraps() {
        let mut p = Poly {coeffs: [0u16; N]};
        let mut q = Poly {coeffs: [0u16; N]};
        p.coeffs[0] = 3328;
        q.coeffs[0] = 1;
        let result = poly_add_Q(&p,&q);
        assert_eq!(result.coeffs[0],0);
    }

    #[test]
    fn test_poly_sub_wraps_correctly() {
        let mut p = Poly {coeffs: [0u16; N]};
        let mut q = Poly {coeffs: [0u16; N]};
        p.coeffs[0] = 0;
        q.coeffs[0] = 1;
        let result = poly_sub_Q(&p, &q);
        assert_eq!(result.coeffs[0], 3328);
    }

}//tests
}//verus!
