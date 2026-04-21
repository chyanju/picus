//! Finite field GF(p) wrapper using feanor-math.
//!
//! Uses `zn_big::Zn` wrapped in `AsField` to satisfy the `Field` trait
//! required by `buchberger_simple`.

use feanor_math::ring::*;
use feanor_math::homomorphism::*;
use feanor_math::rings::zn::zn_big;
use feanor_math::rings::zn::ZnRingStore;
use feanor_math::rings::rust_bigint::*;
use feanor_math::rings::field::AsField;
use feanor_math::delegate::DelegateRing;
use num_bigint::BigUint;

/// The Zn ring type.
pub type ZnRingType = zn_big::Zn<RustBigintRing>;
/// The field type (Zn wrapped as Field).
pub type FfFieldType = AsField<ZnRingType>;
/// A field element.
pub type FfEl = El<FfFieldType>;

/// Convert `num_bigint::BigUint` to feanor-math `BigInt`.
pub fn biguint_to_feanor(n: &BigUint) -> El<RustBigintRing> {
    let zz = RustBigintRing::RING;
    let s = n.to_string();
    if let Ok(small) = s.parse::<i32>() {
        zz.int_hom().map(small)
    } else {
        let mut result = zz.zero();
        let ten = zz.int_hom().map(10);
        for ch in s.chars() {
            let digit = zz.int_hom().map(ch.to_digit(10).unwrap() as i32);
            result = zz.add(zz.mul(result, zz.clone_el(&ten)), digit);
        }
        result
    }
}

/// Convert feanor-math `BigInt` to `num_bigint::BigUint`.
pub fn feanor_to_biguint(n: &El<RustBigintRing>) -> BigUint {
    let zz = RustBigintRing::RING;
    let s = format!("{}", zz.format(n));
    s.parse::<BigUint>().unwrap()
}

/// A finite field GF(p) backed by feanor-math.
pub struct FfField {
    pub prime: BigUint,
    field: FfFieldType,
    zn: ZnRingType,
}

impl FfField {
    pub fn new(prime: &BigUint) -> Self {
        let p_feanor = biguint_to_feanor(prime);
        let zn = zn_big::Zn::new(RustBigintRing::RING, p_feanor);
        let field = zn.clone().as_field().ok().expect("modulus must be prime");
        FfField { prime: prime.clone(), field, zn }
    }

    pub fn field(&self) -> &FfFieldType { &self.field }

    /// Map a `BigUint` into this field.
    pub fn from_biguint(&self, n: &BigUint) -> FfEl {
        let val = biguint_to_feanor(n);
        let hom = self.field.can_hom(&RustBigintRing::RING).unwrap();
        hom.map(val)
    }

    /// Map a field element back to `BigUint`.
    pub fn to_biguint(&self, el: &FfEl) -> BigUint {
        // Unwrap the FieldEl to get the underlying ZnEl
        let zn_el = self.field.get_ring().delegate(self.field.clone_el(el));
        let lifted = self.zn.smallest_positive_lift(zn_el);
        feanor_to_biguint(&lifted)
    }

    pub fn zero(&self) -> FfEl { self.field.zero() }
    pub fn one(&self) -> FfEl { self.field.one() }
    pub fn is_zero(&self, el: &FfEl) -> bool { self.field.is_zero(el) }
    pub fn from_int(&self, n: i32) -> FfEl { self.field.int_hom().map(n) }
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
        let c = r.add(a, b);
        assert_eq!(ff.to_biguint(&c), BigUint::from(5u32));

        let x = ff.from_biguint(&BigUint::from(3u32));
        let y = ff.from_biguint(&BigUint::from(6u32));
        let z = r.mul(x, y);
        assert_eq!(ff.to_biguint(&z), BigUint::from(1u32));
    }

    #[test]
    fn test_bn128_field() {
        let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
        let ff = FfField::new(&p);
        let r = ff.field();

        let a = ff.from_biguint(&(&p - BigUint::from(1u32)));
        let b = ff.from_int(1);
        let c = r.add(a, b);
        assert!(ff.is_zero(&c));
    }
}
