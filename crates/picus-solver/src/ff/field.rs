//! Prime field GF(p) backed by GMP via the `rug` crate.
//!
//! Field elements are stored in canonical (least non-negative) form in
//! `[0, p)`. All arithmetic dispatches to GMP (`mpz_add`, `mpz_mul`,
//! `mpz_mod`, `mpz_invert`, ...) for Karatsuba/Toom-Cook multiplication
//! and platform-specific assembly. This is the same arithmetic backend
//! cvc5+CoCoA uses (`include/CoCoA/BigInt.H:41`).
//!
//! The public API still exchanges `num_bigint::BigUint` at the boundary
//! (encoder input, model output) for compatibility with the rest of the
//! picus workspace. Conversions go through byte order via
//! `to_bytes_le` / `from_bytes_le`.

use num_bigint::BigUint;
use rug::Integer;
use std::sync::Arc;

// ─────────────────────────── BigUint ↔ Integer ───────────────────────────

/// Convert a `BigUint` to a `rug::Integer`. Used at the picus-solver API
/// boundary; not on the hot reduction path.
#[inline]
fn biguint_to_integer(b: &BigUint) -> Integer {
    let bytes = b.to_bytes_le();
    Integer::from_digits(&bytes, rug::integer::Order::Lsf)
}

/// Convert a `rug::Integer` (assumed non-negative) to a `BigUint`.
#[inline]
fn integer_to_biguint(i: &Integer) -> BigUint {
    let bytes: Vec<u8> = i.to_digits::<u8>(rug::integer::Order::Lsf);
    BigUint::from_bytes_le(&bytes)
}

// ───────────────────────────── FieldElem ────────────────────────────────

/// An element of GF(p). Always stored in canonical form `0 <= value < p`.
#[derive(Clone, Debug)]
pub struct FieldElem {
    pub(crate) value: Integer,
}

impl FieldElem {
    /// Direct constructor; caller must ensure `0 <= value < p`.
    #[inline]
    pub(crate) fn new_unchecked(value: Integer) -> Self {
        FieldElem { value }
    }

    /// Borrow the underlying `rug::Integer`. Internal hot-path access.
    #[inline]
    pub fn as_integer(&self) -> &Integer {
        &self.value
    }

    /// Boundary conversion: produce a `BigUint` copy of the value. Allocates;
    /// keep off the hot path.
    pub fn as_biguint(&self) -> BigUint {
        integer_to_biguint(&self.value)
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
        // Hash via byte representation for stability across platforms.
        let bytes: Vec<u8> = self.value.to_digits::<u8>(rug::integer::Order::Lsf);
        bytes.hash(state)
    }
}

// ──────────────────────────── PrimeField ────────────────────────────────

/// A prime field GF(p). Cheaply cloneable (shares the prime via `Arc`).
///
/// We carry both the `rug::Integer` form (for hot-path arithmetic) and
/// the `BigUint` form (for the public boundary API `prime() -> &BigUint`).
/// The prime is constructed once per solve so the duplication cost is
/// negligible.
#[derive(Clone, Debug)]
pub struct PrimeField {
    prime: Arc<Integer>,
    prime_bu: Arc<BigUint>,
    /// Bit width of the prime, cached at construction. Used to size GMP
    /// `Integer` allocations so arithmetic operations (`add`, `sub`,
    /// `mul`, `neg`) produce results that fit without an `mpz_realloc`
    /// — for BN128 (254 bits = 4 limbs) the default `mpz_init` capacity
    /// is one limb and every fresh result paid a realloc.
    result_bits: usize,
    /// Bit width sufficient to hold a product of two prime-sized integers
    /// (`2 * prime_bits + a small margin`). Used by `mul` before the
    /// `% prime` reduction.
    product_bits: usize,
}

impl PrimeField {
    /// Construct a new prime field. Caller is responsible for ensuring
    /// `prime` is actually prime — this constructor does not test
    /// primality.
    pub fn new(prime: BigUint) -> Self {
        assert!(prime > BigUint::from(1u32), "prime must be > 1");
        let prime_int = biguint_to_integer(&prime);
        let result_bits = prime_int.significant_bits() as usize + 1;
        let product_bits = 2 * (prime_int.significant_bits() as usize) + 1;
        PrimeField {
            prime: Arc::new(prime_int),
            prime_bu: Arc::new(prime),
            result_bits,
            product_bits,
        }
    }

    /// The prime modulus (boundary view). Returns the cached `BigUint`
    /// form — no allocation.
    #[inline]
    pub fn prime(&self) -> &BigUint {
        &self.prime_bu
    }

    /// Same as `prime`; provided for API parity.
    #[inline]
    pub fn characteristic(&self) -> &BigUint {
        &self.prime_bu
    }

    /// Internal hot-path access to the prime in `rug::Integer` form.
    #[allow(dead_code)]
    #[inline]
    pub(crate) fn prime_integer(&self) -> &Integer {
        &self.prime
    }

    #[inline]
    pub fn zero(&self) -> FieldElem {
        FieldElem::new_unchecked(Integer::new())
    }

    #[inline]
    pub fn one(&self) -> FieldElem {
        FieldElem::new_unchecked(Integer::from(1))
    }

    pub fn from_u64(&self, v: u64) -> FieldElem {
        let mut val = Integer::from(v);
        val %= &*self.prime;
        FieldElem::new_unchecked(val)
    }

    /// Map a signed integer into the field (negatives become `p - |v|`).
    pub fn from_i64(&self, v: i64) -> FieldElem {
        let mut val = Integer::from(v);
        val %= &*self.prime;
        if val.cmp0() == std::cmp::Ordering::Less {
            val += &*self.prime;
        }
        FieldElem::new_unchecked(val)
    }

    pub fn from_biguint(&self, v: &BigUint) -> FieldElem {
        let mut val = biguint_to_integer(v);
        val %= &*self.prime;
        FieldElem::new_unchecked(val)
    }

    #[inline]
    pub fn to_biguint(&self, e: &FieldElem) -> BigUint {
        integer_to_biguint(&e.value)
    }

    pub fn add(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let mut s = Integer::with_capacity(self.result_bits);
        s.assign(&a.value + &b.value);
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
        let mut r = Integer::with_capacity(self.result_bits);
        r.assign(&a.value - &b.value);
        if r.cmp0() == std::cmp::Ordering::Less {
            r += &*self.prime;
        }
        FieldElem::new_unchecked(r)
    }

    pub fn sub_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        a.value -= &b.value;
        if a.value.cmp0() == std::cmp::Ordering::Less {
            a.value += &*self.prime;
        }
    }

    pub fn mul(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let mut p = Integer::with_capacity(self.product_bits);
        p.assign(&a.value * &b.value);
        p %= &*self.prime;
        FieldElem::new_unchecked(p)
    }

    pub fn mul_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        a.value *= &b.value;
        a.value %= &*self.prime;
    }

    pub fn neg(&self, a: &FieldElem) -> FieldElem {
        if a.value.cmp0() == std::cmp::Ordering::Equal {
            self.zero()
        } else {
            FieldElem::new_unchecked(Integer::from(&*self.prime - &a.value))
        }
    }

    /// Multiplicative inverse via GMP's `mpz_invert`. Returns `None` if
    /// `a` is zero (or if for any reason gcd(a, p) ≠ 1, which should not
    /// happen for a prime modulus and nonzero input).
    pub fn inv(&self, a: &FieldElem) -> Option<FieldElem> {
        if a.value.cmp0() == std::cmp::Ordering::Equal {
            return None;
        }
        match a.value.clone().invert(&self.prime) {
            Ok(v) => Some(FieldElem::new_unchecked(v)),
            Err(_) => None,
        }
    }

    pub fn div(&self, a: &FieldElem, b: &FieldElem) -> Option<FieldElem> {
        let b_inv = self.inv(b)?;
        Some(self.mul(a, &b_inv))
    }

    #[inline]
    pub fn is_zero(&self, a: &FieldElem) -> bool {
        a.value.cmp0() == std::cmp::Ordering::Equal
    }

    #[inline]
    pub fn is_one(&self, a: &FieldElem) -> bool {
        a.value == 1
    }

    #[inline]
    pub fn eq(&self, a: &FieldElem, b: &FieldElem) -> bool {
        a.value == b.value
    }

    /// Modular exponentiation `a^exp mod p` via GMP's `mpz_powm`.
    pub fn pow(&self, a: &FieldElem, exp: &BigUint) -> FieldElem {
        if exp == &BigUint::from(0u32) {
            return self.one();
        }
        let exp_int = biguint_to_integer(exp);
        let mut out = Integer::new();
        out.assign(a.value.pow_mod_ref(&exp_int, &self.prime).unwrap());
        FieldElem::new_unchecked(out)
    }

    /// Modular exponentiation by a `u64` exponent.
    pub fn pow_u64(&self, a: &FieldElem, exp: u64) -> FieldElem {
        if exp == 0 {
            return self.one();
        }
        let exp_int = Integer::from(exp);
        let mut out = Integer::new();
        out.assign(a.value.pow_mod_ref(&exp_int, &self.prime).unwrap());
        FieldElem::new_unchecked(out)
    }

    /// Modular exponentiation by a `rug::Integer` exponent — internal
    /// hot path (avoids BigUint conversion when the caller already has
    /// the exponent in `Integer` form).
    #[allow(dead_code)]
    pub(crate) fn pow_integer(&self, a: &FieldElem, exp: &Integer) -> FieldElem {
        if exp.cmp0() == std::cmp::Ordering::Equal {
            return self.one();
        }
        let mut out = Integer::new();
        out.assign(a.value.pow_mod_ref(exp, &self.prime).unwrap());
        FieldElem::new_unchecked(out)
    }

    /// Clone an element. Provided for API parity.
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
    #[inline]
    pub fn int_hom(&self) -> IntHom<'_> {
        IntHom { field: self }
    }
}

use rug::Assign;

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
        assert_eq!(f.to_biguint(&f.from_i64(-1)), BigUint::from(6u32));
        assert_eq!(f.to_biguint(&f.from_i64(-7)), BigUint::from(0u32));
        assert_eq!(f.to_biguint(&f.from_i64(-8)), BigUint::from(6u32));
    }

    #[test]
    fn neg_works() {
        let f = PrimeField::new(BigUint::from(7u32));
        let a = f.from_u64(3);
        let na = f.neg(&a);
        assert_eq!(f.to_biguint(&na), BigUint::from(4u32));
        assert!(f.is_zero(&f.add(&a, &na)));
        assert!(f.is_zero(&f.neg(&f.zero())));
    }

    #[test]
    fn fermat_pow_bn128() {
        let p = bn128();
        let f = PrimeField::new(p.clone());
        // a^(p-1) = 1 for any a != 0
        let a = f.from_u64(2);
        let exp = &p - BigUint::from(1u32);
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
