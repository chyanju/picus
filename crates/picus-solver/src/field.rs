//! Finite field GF(p) — re-exports from [`crate::ff::field`].
//!
//! `FfField` is a type alias for [`PrimeField`]; callers reach the
//! prime via [`PrimeField::prime`].

pub use crate::ff::field::{FieldElem as FfEl, PrimeField};

/// Finite field GF(p). Alias for [`PrimeField`].
pub type FfField = PrimeField;

/// Compatibility alias; identical to [`FfField`].
pub type FfFieldType = PrimeField;

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_basic_field_ops() {
        let p = BigUint::from(17u32);
        let ff = FfField::new(p);

        let a = ff.from_biguint(&BigUint::from(10u32));
        let b = ff.from_biguint(&BigUint::from(12u32));
        let c = ff.add(&a, &b);
        assert_eq!(ff.to_biguint(&c), BigUint::from(5u32));

        let x = ff.from_biguint(&BigUint::from(3u32));
        let y = ff.from_biguint(&BigUint::from(6u32));
        let z = ff.mul(&x, &y);
        assert_eq!(ff.to_biguint(&z), BigUint::from(1u32));
    }

    #[test]
    fn test_bn128_field() {
        let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
        let ff = FfField::new(p.clone());

        let a = ff.from_biguint(&(&p - BigUint::from(1u32)));
        let b = ff.from_int(1);
        let c = ff.add(&a, &b);
        assert!(ff.is_zero(&c));
    }
}
