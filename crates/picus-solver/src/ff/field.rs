//! Prime field GF(p) for arbitrary primes (sized for BN128 ~254 bits).
//!
//! Internal representation is `num_bigint::BigUint`. Field elements are stored
//! in canonical (least non-negative) form in `[0, p)`.
//!
//! All arithmetic is performed using `BigUint` operations followed by reduction.
//! This is sufficient: earlier profiling identified the dominant costs as
//! branching strategy and polynomial arithmetic, not per-operation
//! field-element cost. Montgomery form can be added later as a separate
//! optimization.

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};
use std::sync::Arc;

/// An element of GF(p). Always stored in canonical form `0 <= value < p`.
#[derive(Clone, Debug)]
pub struct FieldElem {
    pub(crate) value: BigUint,
}

impl FieldElem {
    /// Direct constructor; caller must ensure `value < p`.
    #[inline]
    pub(crate) fn new_unchecked(value: BigUint) -> Self {
        FieldElem { value }
    }

    /// Borrow the underlying canonical representative.
    #[inline]
    pub fn as_biguint(&self) -> &BigUint {
        &self.value
    }
}

impl PartialEq for FieldElem {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl Eq for FieldElem {}

impl std::hash::Hash for FieldElem {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

/// A prime field GF(p). Cheaply cloneable (shares the prime via `Arc`).
#[derive(Clone, Debug)]
pub struct PrimeField {
    prime: Arc<BigUint>,
}

impl PrimeField {
    /// Construct a new prime field. Caller is responsible for ensuring `prime`
    /// is actually prime — this constructor does not test primality.
    pub fn new(prime: BigUint) -> Self {
        assert!(prime > BigUint::one(), "prime must be > 1");
        PrimeField { prime: Arc::new(prime) }
    }

    /// The prime modulus.
    #[inline]
    pub fn prime(&self) -> &BigUint {
        &self.prime
    }

    /// Same as `prime`; provided for API parity with feanor-math `Field` trait.
    #[inline]
    pub fn characteristic(&self) -> &BigUint {
        &self.prime
    }

    #[inline]
    pub fn zero(&self) -> FieldElem {
        FieldElem::new_unchecked(BigUint::zero())
    }

    #[inline]
    pub fn one(&self) -> FieldElem {
        FieldElem::new_unchecked(BigUint::one())
    }

    pub fn from_u64(&self, v: u64) -> FieldElem {
        let val = BigUint::from(v);
        FieldElem::new_unchecked(val % &*self.prime)
    }

    /// Map a signed integer into the field (negatives become `p - |v|`).
    pub fn from_i64(&self, v: i64) -> FieldElem {
        if v >= 0 {
            self.from_u64(v as u64)
        } else {
            let abs_val = BigUint::from(v.unsigned_abs());
            let r = &*self.prime - (abs_val % &*self.prime);
            if r == *self.prime {
                self.zero()
            } else {
                FieldElem::new_unchecked(r)
            }
        }
    }

    pub fn from_biguint(&self, v: &BigUint) -> FieldElem {
        FieldElem::new_unchecked(v % &*self.prime)
    }

    #[inline]
    pub fn to_biguint(&self, e: &FieldElem) -> BigUint {
        e.value.clone()
    }

    pub fn add(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let mut s = &a.value + &b.value;
        if s >= *self.prime {
            s -= &*self.prime;
        }
        FieldElem::new_unchecked(s)
    }

    pub fn add_assign<B: std::borrow::Borrow<FieldElem>>(&self, a: &mut FieldElem, b: B) {
        let b = b.borrow();
        a.value += &b.value;
        if a.value >= *self.prime {
            a.value -= &*self.prime;
        }
    }

    /// Kept for symmetry / clarity — equivalent to `add_assign(a, b)`.
    pub fn add_assign_owned(&self, a: &mut FieldElem, b: FieldElem) {
        self.add_assign(a, &b)
    }

    pub fn sub(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        if a.value >= b.value {
            FieldElem::new_unchecked(&a.value - &b.value)
        } else {
            FieldElem::new_unchecked(&*self.prime - (&b.value - &a.value))
        }
    }

    pub fn sub_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        if a.value >= b.value {
            a.value -= &b.value;
        } else {
            // a < b => result = p - (b - a)
            let diff = &b.value - &a.value;
            a.value = &*self.prime - diff;
        }
    }

    pub fn mul(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        FieldElem::new_unchecked((&a.value * &b.value) % &*self.prime)
    }

    pub fn mul_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        a.value = (&a.value * &b.value) % &*self.prime;
    }

    pub fn neg(&self, a: &FieldElem) -> FieldElem {
        if a.value.is_zero() {
            self.zero()
        } else {
            FieldElem::new_unchecked(&*self.prime - &a.value)
        }
    }

    /// Multiplicative inverse via the extended Euclidean algorithm.
    /// Returns `None` if `a` is zero.
    pub fn inv(&self, a: &FieldElem) -> Option<FieldElem> {
        if a.value.is_zero() {
            return None;
        }
        // Use signed extended GCD on BigInts.
        use num_bigint::BigInt;
        let p_int: BigInt = (*self.prime).clone().into();
        let a_int: BigInt = a.value.clone().into();
        let egcd = a_int.extended_gcd(&p_int);
        if egcd.gcd != BigInt::one() {
            // Should not happen for a prime modulus & nonzero a.
            return None;
        }
        // Reduce x mod p to canonical positive.
        let mut x = egcd.x % &p_int;
        if x.sign() == num_bigint::Sign::Minus {
            x += &p_int;
        }
        let (_, mag) = x.into_parts();
        Some(FieldElem::new_unchecked(mag))
    }

    pub fn div(&self, a: &FieldElem, b: &FieldElem) -> Option<FieldElem> {
        let b_inv = self.inv(b)?;
        Some(self.mul(a, &b_inv))
    }

    #[inline]
    pub fn is_zero(&self, a: &FieldElem) -> bool {
        a.value.is_zero()
    }

    #[inline]
    pub fn is_one(&self, a: &FieldElem) -> bool {
        a.value.is_one()
    }

    #[inline]
    pub fn eq(&self, a: &FieldElem, b: &FieldElem) -> bool {
        a.value == b.value
    }

    /// Modular exponentiation `a^exp mod p` (square-and-multiply).
    pub fn pow(&self, a: &FieldElem, exp: &BigUint) -> FieldElem {
        if exp.is_zero() {
            return self.one();
        }
        let v = a.value.modpow(exp, &*self.prime);
        FieldElem::new_unchecked(v)
    }

    /// Modular exponentiation by a `u64` exponent.
    pub fn pow_u64(&self, a: &FieldElem, exp: u64) -> FieldElem {
        let e = BigUint::from(exp);
        self.pow(a, &e)
    }

    /// Clone an element. Provided for API parity with feanor-math style.
    #[inline]
    pub fn clone_el(&self, a: &FieldElem) -> FieldElem {
        a.clone()
    }

    // ---- Legacy aliases (feanor-math `RingBase`-style names) ----
    // DEPRECATED: prefer the canonical methods (`eq`, `neg`, `mul`, `add`,
    // `sub`, `from_i64`, `.clone()`). These wrappers exist only for
    // migration convenience and will be removed in a future release.

    /// Alias for `eq` (feanor-style name).
    #[inline]
    pub fn eq_el(&self, a: &FieldElem, b: &FieldElem) -> bool {
        self.eq(a, b)
    }

    /// Negate by-value (feanor-style: consumes input). Equivalent to `neg(&a)`.
    #[inline]
    pub fn negate(&self, a: FieldElem) -> FieldElem {
        self.neg(&a)
    }

    /// Multiply by reference, returning a new element.
    #[inline]
    pub fn mul_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.mul(a, b)
    }

    /// Add by reference.
    #[inline]
    pub fn add_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.add(a, b)
    }

    /// Subtract by reference.
    #[inline]
    pub fn sub_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.sub(a, b)
    }

    /// `from_int(n)` analog for any integer type.
    #[inline]
    pub fn from_int(&self, n: i64) -> FieldElem {
        self.from_i64(n)
    }

    /// Returns a homomorphism object whose `.map(n)` constructs `n` in the field.
    /// Provided for compatibility with `field.int_hom().map(2)` calling style.
    #[inline]
    pub fn int_hom(&self) -> IntHom<'_> {
        IntHom { field: self }
    }
}

/// Helper for `field.int_hom().map(n)` ergonomics (mirrors feanor's `IntHom`).
pub struct IntHom<'a> {
    field: &'a PrimeField,
}

impl<'a> IntHom<'a> {
    #[inline]
    pub fn map(&self, n: i64) -> FieldElem {
        self.field.from_i64(n)
    }
}

impl PartialEq for PrimeField {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.prime, &other.prime) || *self.prime == *other.prime
    }
}
impl Eq for PrimeField {}

#[cfg(test)]
mod tests {
    use super::*;

    fn bn128() -> BigUint {
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse()
            .unwrap()
    }

    #[test]
    fn small_prime_basics() {
        let f = PrimeField::new(BigUint::from(17u32));
        let a = f.from_u64(10);
        let b = f.from_u64(12);
        let c = f.add(&a, &b);
        assert_eq!(f.to_biguint(&c), BigUint::from(5u32));

        let x = f.from_u64(3);
        let y = f.from_u64(6);
        assert_eq!(f.to_biguint(&f.mul(&x, &y)), BigUint::from(1u32));

        // Inverse: 3 * 6 = 18 = 1 mod 17, so 3^-1 = 6.
        assert_eq!(f.inv(&x).unwrap(), y);

        // Division.
        let d = f.div(&f.from_u64(1), &x).unwrap();
        assert_eq!(d, y);
    }

    #[test]
    fn sub_underflow() {
        let f = PrimeField::new(BigUint::from(7u32));
        let a = f.from_u64(2);
        let b = f.from_u64(5);
        let c = f.sub(&a, &b);
        // 2 - 5 = -3 mod 7 = 4
        assert_eq!(f.to_biguint(&c), BigUint::from(4u32));

        let mut a2 = f.from_u64(2);
        f.sub_assign(&mut a2, &b);
        assert_eq!(f.to_biguint(&a2), BigUint::from(4u32));
    }

    #[test]
    fn from_i64_negative() {
        let f = PrimeField::new(BigUint::from(7u32));
        assert_eq!(f.from_i64(-1).value, BigUint::from(6u32));
        assert_eq!(f.from_i64(-7).value, BigUint::from(0u32));
        assert_eq!(f.from_i64(-8).value, BigUint::from(6u32));
    }

    #[test]
    fn neg_works() {
        let f = PrimeField::new(BigUint::from(7u32));
        let a = f.from_u64(3);
        let na = f.neg(&a);
        assert_eq!(na.value, BigUint::from(4u32));
        assert!(f.is_zero(&f.add(&a, &na)));
        assert!(f.is_zero(&f.neg(&f.zero())));
    }

    #[test]
    fn fermat_pow_bn128() {
        let p = bn128();
        let f = PrimeField::new(p.clone());
        // a^(p-1) = 1 for any a != 0
        let a = f.from_u64(2);
        let exp = &p - BigUint::one();
        let res = f.pow(&a, &exp);
        assert!(f.is_one(&res));
    }

    #[test]
    fn inverse_bn128() {
        let p = bn128();
        let f = PrimeField::new(p.clone());
        let a = f.from_u64(123456789);
        let ai = f.inv(&a).unwrap();
        assert!(f.is_one(&f.mul(&a, &ai)));
    }

    #[test]
    fn axioms_random() {
        // Random axiom check at small modulus
        let f = PrimeField::new(BigUint::from(101u32));
        for x in 0u64..101 {
            for y in 0u64..101 {
                let a = f.from_u64(x);
                let b = f.from_u64(y);
                // commutativity
                assert_eq!(f.add(&a, &b), f.add(&b, &a));
                assert_eq!(f.mul(&a, &b), f.mul(&b, &a));
                // additive inverse
                assert!(f.is_zero(&f.add(&a, &f.neg(&a))));
            }
        }
    }
}
