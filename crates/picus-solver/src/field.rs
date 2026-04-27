//! Finite field GF(p) wrapper.
//!
//! Now backed by `crate::ff::PrimeField` (the inlined replacement for
//! `feanor-math`'s `Zn`/`AsField`). The public type names (`FfField`,
//! `FfEl`) are preserved as compatibility re-exports for the rest of the
//! crate.

use num_bigint::BigUint;

pub use crate::ff::field::{FieldElem as FfEl, PrimeField as FfFieldType};

/// A finite field GF(p).
///
/// Thin wrapper around `ff::PrimeField` that preserves the public API of the
/// pre-`ff` implementation: callers can keep using `FfField::new(&p)`,
/// `ff.from_biguint(&n)`, `ff.to_biguint(&el)`, `ff.field()` (which used to
/// return the underlying feanor ring), and the trivial helpers
/// `zero/one/is_zero/from_int`.
pub struct FfField {
    pub prime: BigUint,
    field: FfFieldType,
}

impl FfField {
    pub fn new(prime: &BigUint) -> Self {
        let field = FfFieldType::new(prime.clone());
        FfField { prime: prime.clone(), field }
    }

    /// Reference to the underlying `PrimeField` for direct arithmetic
    /// (`field.add(&a, &b)`, `field.mul(&a, &b)`, `field.inv(&a)`, ...).
    pub fn field(&self) -> &FfFieldType { &self.field }

    /// Map a `BigUint` into this field.
    pub fn from_biguint(&self, n: &BigUint) -> FfEl {
        self.field.from_biguint(n)
    }

    /// Map a field element back to `BigUint`.
    pub fn to_biguint(&self, el: &FfEl) -> BigUint {
        self.field.to_biguint(el)
    }

    pub fn zero(&self) -> FfEl { self.field.zero() }
    pub fn one(&self) -> FfEl { self.field.one() }
    pub fn is_zero(&self, el: &FfEl) -> bool { self.field.is_zero(el) }
    pub fn from_int(&self, n: i32) -> FfEl { self.field.from_i64(n as i64) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_field_ops() {
        let p = BigUint::from(17u32);
        let ff = FfField::new(&p);
        let r = ff.field();

        let a = ff.from_biguint(&BigUint::from(10u32));
        let b = ff.from_biguint(&BigUint::from(12u32));
        let c = r.add(&a, &b);
        assert_eq!(ff.to_biguint(&c), BigUint::from(5u32));

        let x = ff.from_biguint(&BigUint::from(3u32));
        let y = ff.from_biguint(&BigUint::from(6u32));
        let z = r.mul(&x, &y);
        assert_eq!(ff.to_biguint(&z), BigUint::from(1u32));
    }

    #[test]
    fn test_bn128_field() {
        let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
        let ff = FfField::new(&p);
        let r = ff.field();

        let a = ff.from_biguint(&(&p - BigUint::from(1u32)));
        let b = ff.from_int(1);
        let c = r.add(&a, &b);
        assert!(ff.is_zero(&c));
    }
}
