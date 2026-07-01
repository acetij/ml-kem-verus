/*barret.rs
 * Johnny K. Aceti
 */

use crate::arith::Q;
use vstd::prelude::*;

verus! {
    

    //Barret Reduction (mod Q = 3329)
    pub fn barret_reduce_Q(r: u32) -> u32 {
        const SHIFT: usize = 26;
        const MULTIPLIER: u32 = 20159;
        let quotient = ((r as u64 * MULTIPLIER as u64) >> SHIFT) as u32;
        let remainder = r - quotient * Q;
        //Constant-time reduct
        let result = if remainder >= Q {remainder - Q} else {remainder};
        result
    }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_barret_zero() {
        assert_eq!(barret_reduce_Q(0),0);
    }

    #[test]
    fn test_barrett_at_Q() {
        assert_eq!(barret_reduce_Q(Q), 0);
    }

    #[test]
    fn test_barret_Q_plus_one() {
        assert_eq!(barret_reduce_Q(Q + 1), 1);
    }

    //Maximum possible input for ML-KEM
    //Largest product of two coefficients: 3328^2
    #[test]
    fn test_barret_max_product() {
        let max = 3328u32 * 3328u32;
        let result = barret_reduce_Q(max);
        assert_eq!(result, (max % Q));
        assert!(result < Q);
    }

    //2*Q - 1 (largest value before double Q)
    fn test_barret_two_Q_minus_one() {
        let input = 2*Q - 1;
        assert_eq!(barret_reduce_Q(input), (input % Q));
    }




}//tests




}//verus!

