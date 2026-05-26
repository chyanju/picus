//! Prime field GF(p) with two backends.
//!
//! [`PrimeField::new`] selects at construction time:
//!
//! * `bits(prime) <= 64`: u64 representative with u128 product buffer.
//!   Modular arithmetic compiles to a handful of machine instructions
//!   per op. No allocations.
//! * Otherwise: `rug::Integer` (GMP). Thread-local pool recycles
//!   `mpz_t` limb buffers across the geobucket cascade.
//!
//! Field elements are stored in canonical (least non-negative) form
//! in `[0, p)`. Boundary I/O goes through [`num_bigint::BigUint`] via
//! byte-order conversion.

use num_bigint::BigUint;
use rug::Integer;
use std::sync::Arc;

// ─────────────────────────── BigUint ↔ Integer ───────────────────────────

#[inline]
fn biguint_to_integer(b: &BigUint) -> Integer {
    let bytes = b.to_bytes_le();
    Integer::from_digits(&bytes, rug::integer::Order::Lsf)
}

#[inline]
fn integer_to_biguint(i: &Integer) -> BigUint {
    let bytes: Vec<u8> = i.to_digits::<u8>(rug::integer::Order::Lsf);
    BigUint::from_bytes_le(&bytes)
}

#[inline]
fn biguint_to_u64(b: &BigUint) -> Option<u64> {
    let digits = b.to_u64_digits();
    match digits.len() {
        0 => Some(0),
        1 => Some(digits[0]),
        _ => None,
    }
}

// ───────────────────────────── FieldElem ────────────────────────────────

/// An element of GF(p). Always stored in canonical form `0 <= value < p`.
///
/// The backing representation is chosen by the field at construction:
/// a `u64` for primes `<= 2^64`, otherwise a `rug::Integer`. Elements
/// from different fields are not interchangeable; the corresponding
/// `PrimeField` must be used for every operation.
#[derive(Debug)]
pub struct FieldElem {
    repr: ElemRepr,
}

#[derive(Debug)]
enum ElemRepr {
    Gmp(Integer),
    Small(u64),
}

impl FieldElem {
    #[inline]
    pub fn from_integer_unchecked(value: Integer) -> Self {
        FieldElem { repr: ElemRepr::Gmp(value) }
    }

    #[inline]
    pub fn from_u64_unchecked(value: u64) -> Self {
        FieldElem { repr: ElemRepr::Small(value) }
    }

    /// Convert to `BigUint`. Allocates.
    pub fn as_biguint(&self) -> BigUint {
        match &self.repr {
            ElemRepr::Gmp(v) => integer_to_biguint(v),
            ElemRepr::Small(v) => BigUint::from(*v),
        }
    }

    #[inline]
    fn as_gmp(&self) -> &Integer {
        match &self.repr {
            ElemRepr::Gmp(v) => v,
            ElemRepr::Small(_) => unreachable!("FieldElem variant mismatch: expected Gmp"),
        }
    }

    #[inline]
    fn as_gmp_mut(&mut self) -> &mut Integer {
        match &mut self.repr {
            ElemRepr::Gmp(v) => v,
            ElemRepr::Small(_) => unreachable!("FieldElem variant mismatch: expected Gmp"),
        }
    }

    #[inline]
    fn as_small(&self) -> u64 {
        match &self.repr {
            ElemRepr::Small(v) => *v,
            ElemRepr::Gmp(_) => unreachable!("FieldElem variant mismatch: expected Small"),
        }
    }

    /// Take a recycled Gmp `FieldElem` from the thread-local pool;
    /// allocates fresh on miss with `capacity_bits` reserved. The
    /// returned element's value is uninitialised — caller must
    /// `assign` before reading. Gmp backend only.
    #[inline]
    fn pool_take_or_default_gmp(capacity_bits: u32) -> Self {
        FIELDELEM_POOL.with(|pool| {
            if let Some(mut e) = pool.borrow_mut().pop() {
                if let ElemRepr::Gmp(ref mut v) = e.repr {
                    if (v.capacity() as u32) < capacity_bits {
                        v.reserve(capacity_bits as usize);
                    }
                }
                e
            } else {
                FieldElem {
                    repr: ElemRepr::Gmp(Integer::with_capacity(capacity_bits as usize)),
                }
            }
        })
    }

    /// Return a Gmp-backed `FieldElem` to the pool. No-op for Small.
    #[inline]
    fn pool_return(self) {
        match self.repr {
            ElemRepr::Gmp(_) => {
                FIELDELEM_POOL.with(|pool| {
                    let mut p = pool.borrow_mut();
                    if p.len() < FIELDELEM_POOL_CAP {
                        p.push(self);
                    }
                });
            }
            ElemRepr::Small(_) => {
                // u64 has no heap-backed resource to recycle.
            }
        }
    }
}

const FIELDELEM_POOL_CAP: usize = 4096;

thread_local! {
    /// Thread-local pool of recycled Gmp `FieldElem`s. Pool contents
    /// are always `ElemRepr::Gmp(_)`; Small variants do not pool.
    static FIELDELEM_POOL: std::cell::RefCell<Vec<FieldElem>> =
        std::cell::RefCell::new(Vec::with_capacity(FIELDELEM_POOL_CAP / 4));
    /// Re-entrancy guard for `Drop` during thread-local destruction.
    /// `Drop` reads this flag; when set, the impl returns early
    /// without touching `FIELDELEM_POOL`.
    static IN_POOL_DROP: std::cell::Cell<bool> = std::cell::Cell::new(false);
}

impl Drop for FieldElem {
    fn drop(&mut self) {
        if IN_POOL_DROP.with(|c| c.get()) {
            return;
        }
        if let ElemRepr::Gmp(ref mut v) = self.repr {
            let _ = FIELDELEM_POOL.try_with(|pool| {
                if let Ok(mut p) = pool.try_borrow_mut() {
                    if p.len() < FIELDELEM_POOL_CAP {
                        let val = std::mem::replace(v, Integer::new());
                        p.push(FieldElem { repr: ElemRepr::Gmp(val) });
                    }
                }
            });
        }
    }
}

impl Clone for FieldElem {
    fn clone(&self) -> Self {
        match &self.repr {
            ElemRepr::Gmp(v) => FieldElem { repr: ElemRepr::Gmp(v.clone()) },
            ElemRepr::Small(v) => FieldElem { repr: ElemRepr::Small(*v) },
        }
    }
}

impl PartialEq for FieldElem {
    fn eq(&self, other: &Self) -> bool {
        match (&self.repr, &other.repr) {
            (ElemRepr::Gmp(a), ElemRepr::Gmp(b)) => a == b,
            (ElemRepr::Small(a), ElemRepr::Small(b)) => a == b,
            // Cross-variant inputs are unreachable from any
            // `PrimeField` API path (each ring produces one variant).
            // The byte-equality fallback keeps `eq` total without
            // panicking.
            (ElemRepr::Gmp(a), ElemRepr::Small(b)) => &integer_to_biguint(a) == &BigUint::from(*b),
            (ElemRepr::Small(a), ElemRepr::Gmp(b)) => &BigUint::from(*a) == &integer_to_biguint(b),
        }
    }
}

impl Eq for FieldElem {}

impl std::hash::Hash for FieldElem {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.repr {
            ElemRepr::Gmp(v) => {
                let bytes: Vec<u8> = v.to_digits::<u8>(rug::integer::Order::Lsf);
                bytes.hash(state);
            }
            ElemRepr::Small(v) => {
                // Hash the canonical LSB-first byte representation
                // with trailing zero bytes stripped. Matches the GMP
                // path's `to_digits::<u8>` output for equal numeric
                // values, so `Hash` agrees with `PartialEq` across
                // variants.
                let bytes = v.to_le_bytes();
                let mut trimmed: &[u8] = &bytes;
                while trimmed.last() == Some(&0) && !trimmed.is_empty() {
                    trimmed = &trimmed[..trimmed.len() - 1];
                }
                trimmed.hash(state);
            }
        }
    }
}

// ──────────────────────────── PrimeField ────────────────────────────────

/// A prime field GF(p). Cheaply cloneable (shares the prime via `Arc`).
#[derive(Clone, Debug)]
pub struct PrimeField {
    prime_bu: Arc<BigUint>,
    kind: FieldKind,
}

#[derive(Clone, Debug)]
enum FieldKind {
    Gmp {
        prime: Arc<Integer>,
        /// Bit width sufficient for `add` / `sub` / `neg` results.
        result_bits: usize,
        /// Bit width sufficient for the unreduced product `a * b`.
        product_bits: usize,
    },
    Small {
        prime: u64,
    },
}

/// Threshold for selecting the u64 backend. `bits <= 64` means the
/// prime and every element fit in a u64; the product `a * b` then
/// fits in a u128.
const SMALL_PRIME_BITS: u64 = 64;

impl PrimeField {
    /// Construct a new prime field. Auto-selects the u64 backend
    /// when `prime` fits in a u64; falls back to GMP otherwise.
    /// Caller is responsible for ensuring `prime` is prime — this
    /// constructor does not test primality.
    pub fn new(prime: BigUint) -> Self {
        assert!(prime > BigUint::from(1u32), "prime must be > 1");
        if prime.bits() <= SMALL_PRIME_BITS {
            if let Some(p) = biguint_to_u64(&prime) {
                return PrimeField {
                    prime_bu: Arc::new(prime),
                    kind: FieldKind::Small { prime: p },
                };
            }
        }
        let prime_int = biguint_to_integer(&prime);
        let result_bits = prime_int.significant_bits() as usize + 1;
        let product_bits = 2 * (prime_int.significant_bits() as usize) + 1;
        PrimeField {
            prime_bu: Arc::new(prime),
            kind: FieldKind::Gmp {
                prime: Arc::new(prime_int),
                result_bits,
                product_bits,
            },
        }
    }

    #[inline]
    pub fn prime(&self) -> &BigUint {
        &self.prime_bu
    }

    #[inline]
    pub fn characteristic(&self) -> &BigUint {
        &self.prime_bu
    }

    #[inline]
    pub fn zero(&self) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { .. } => FieldElem::from_integer_unchecked(Integer::new()),
            FieldKind::Small { .. } => FieldElem::from_u64_unchecked(0),
        }
    }

    #[inline]
    pub fn one(&self) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { .. } => FieldElem::from_integer_unchecked(Integer::from(1)),
            FieldKind::Small { .. } => FieldElem::from_u64_unchecked(1),
        }
    }

    pub fn from_u64(&self, v: u64) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let mut val = Integer::from(v);
                val %= &**prime;
                FieldElem::from_integer_unchecked(val)
            }
            FieldKind::Small { prime } => FieldElem::from_u64_unchecked(v % prime),
        }
    }

    /// Map a signed integer into the field (negatives become `p - |v|`).
    pub fn from_i64(&self, v: i64) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let mut val = Integer::from(v);
                val %= &**prime;
                if val.cmp0() == std::cmp::Ordering::Less {
                    val += &**prime;
                }
                FieldElem::from_integer_unchecked(val)
            }
            FieldKind::Small { prime } => {
                let p = *prime;
                let r = (v as i128).rem_euclid(p as i128) as u64;
                FieldElem::from_u64_unchecked(r)
            }
        }
    }

    pub fn from_biguint(&self, v: &BigUint) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let mut val = biguint_to_integer(v);
                val %= &**prime;
                FieldElem::from_integer_unchecked(val)
            }
            FieldKind::Small { prime } => {
                let p_bu = BigUint::from(*prime);
                let r = v % &p_bu;
                FieldElem::from_u64_unchecked(
                    biguint_to_u64(&r).expect("reduced value < prime < 2^64 fits u64"),
                )
            }
        }
    }

    #[inline]
    pub fn to_biguint(&self, e: &FieldElem) -> BigUint {
        e.as_biguint()
    }

    pub fn add(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, result_bits, .. } => {
                let mut out = FieldElem::pool_take_or_default_gmp(*result_bits as u32);
                {
                    let out_v = out.as_gmp_mut();
                    out_v.assign(a.as_gmp() + b.as_gmp());
                    if *out_v >= **prime {
                        *out_v -= &**prime;
                    }
                }
                out
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_add(a.as_small(), b.as_small(), *prime))
            }
        }
    }

    pub fn add_assign<B: std::borrow::Borrow<FieldElem>>(&self, a: &mut FieldElem, b: B) {
        let b_ref = b.borrow();
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                *av += b_ref.as_gmp();
                if *av >= **prime {
                    *av -= &**prime;
                }
            }
            FieldKind::Small { prime } => {
                let av = match &mut a.repr {
                    ElemRepr::Small(v) => v,
                    _ => unreachable!(),
                };
                *av = small_add(*av, b_ref.as_small(), *prime);
            }
        }
    }

    /// By-value `b` variant of [`Self::add_assign`].
    pub fn add_assign_owned(&self, a: &mut FieldElem, b: FieldElem) {
        self.add_assign(a, &b)
    }

    pub fn sub(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, result_bits, .. } => {
                let mut out = FieldElem::pool_take_or_default_gmp(*result_bits as u32);
                {
                    let out_v = out.as_gmp_mut();
                    out_v.assign(a.as_gmp() - b.as_gmp());
                    if out_v.cmp0() == std::cmp::Ordering::Less {
                        *out_v += &**prime;
                    }
                }
                out
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_sub(a.as_small(), b.as_small(), *prime))
            }
        }
    }

    pub fn sub_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                *av -= b.as_gmp();
                if av.cmp0() == std::cmp::Ordering::Less {
                    *av += &**prime;
                }
            }
            FieldKind::Small { prime } => {
                let av = match &mut a.repr {
                    ElemRepr::Small(v) => v,
                    _ => unreachable!(),
                };
                *av = small_sub(*av, b.as_small(), *prime);
            }
        }
    }

    pub fn mul(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, product_bits, .. } => {
                let mut out = FieldElem::pool_take_or_default_gmp(*product_bits as u32);
                {
                    let out_v = out.as_gmp_mut();
                    out_v.assign(a.as_gmp() * b.as_gmp());
                    *out_v %= &**prime;
                }
                out
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_mul(a.as_small(), b.as_small(), *prime))
            }
        }
    }

    pub fn mul_assign(&self, a: &mut FieldElem, b: &FieldElem) {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                *av *= b.as_gmp();
                *av %= &**prime;
            }
            FieldKind::Small { prime } => {
                let av = match &mut a.repr {
                    ElemRepr::Small(v) => v,
                    _ => unreachable!(),
                };
                *av = small_mul(*av, b.as_small(), *prime);
            }
        }
    }

    /// In-place add-and-consume that recycles `a`'s buffer (GMP) or
    /// performs a trivial assign (Small). Returns `b` to the pool.
    #[inline]
    pub fn add_owned(&self, mut a: FieldElem, b: FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                *av += b.as_gmp();
                if *av >= **prime {
                    *av -= &**prime;
                }
                b.pool_return();
                a
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_add(a.as_small(), b.as_small(), *prime))
            }
        }
    }

    #[inline]
    pub fn sub_owned(&self, mut a: FieldElem, b: FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                *av -= b.as_gmp();
                if av.cmp0() == std::cmp::Ordering::Less {
                    *av += &**prime;
                }
                b.pool_return();
                a
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_sub(a.as_small(), b.as_small(), *prime))
            }
        }
    }

    /// Negate in place, reusing the buffer.
    #[inline]
    pub fn neg_owned(&self, mut a: FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp_mut();
                if av.cmp0() != std::cmp::Ordering::Equal {
                    let old = std::mem::replace(av, Integer::new());
                    *av = &**prime - old;
                }
                a
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_neg(a.as_small(), *prime))
            }
        }
    }

    pub fn neg(&self, a: &FieldElem) -> FieldElem {
        match &self.kind {
            FieldKind::Gmp { prime, result_bits, .. } => {
                if a.as_gmp().cmp0() == std::cmp::Ordering::Equal {
                    self.zero()
                } else {
                    let mut out = FieldElem::pool_take_or_default_gmp(*result_bits as u32);
                    out.as_gmp_mut().assign(&**prime - a.as_gmp());
                    out
                }
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_neg(a.as_small(), *prime))
            }
        }
    }

    /// Multiplicative inverse. Returns `None` if `a` is zero.
    pub fn inv(&self, a: &FieldElem) -> Option<FieldElem> {
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let av = a.as_gmp();
                if av.cmp0() == std::cmp::Ordering::Equal {
                    return None;
                }
                match av.clone().invert(prime) {
                    Ok(v) => Some(FieldElem::from_integer_unchecked(v)),
                    Err(_) => None,
                }
            }
            FieldKind::Small { prime } => {
                small_inv(a.as_small(), *prime).map(FieldElem::from_u64_unchecked)
            }
        }
    }

    pub fn div(&self, a: &FieldElem, b: &FieldElem) -> Option<FieldElem> {
        let b_inv = self.inv(b)?;
        Some(self.mul(a, &b_inv))
    }

    #[inline]
    pub fn is_zero(&self, a: &FieldElem) -> bool {
        match &a.repr {
            ElemRepr::Gmp(v) => v.cmp0() == std::cmp::Ordering::Equal,
            ElemRepr::Small(v) => *v == 0,
        }
    }

    #[inline]
    pub fn is_one(&self, a: &FieldElem) -> bool {
        match &a.repr {
            ElemRepr::Gmp(v) => *v == 1,
            ElemRepr::Small(v) => *v == 1,
        }
    }

    #[inline]
    pub fn eq(&self, a: &FieldElem, b: &FieldElem) -> bool {
        a == b
    }

    /// Modular exponentiation `a^exp mod p`.
    pub fn pow(&self, a: &FieldElem, exp: &BigUint) -> FieldElem {
        if exp == &BigUint::from(0u32) {
            return self.one();
        }
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let exp_int = biguint_to_integer(exp);
                let mut out = Integer::new();
                out.assign(a.as_gmp().pow_mod_ref(&exp_int, prime).unwrap());
                FieldElem::from_integer_unchecked(out)
            }
            FieldKind::Small { prime } => {
                // Repeated squaring scanning `exp`'s little-endian bit
                // string. Base and result stay in u64; the per-step
                // squaring uses `small_mul` (u128 intermediate). No
                // GMP allocations.
                let mut result: u64 = 1;
                let mut base = a.as_small();
                let p = *prime;
                let bytes = exp.to_bytes_le();
                let mut bit_in_byte = 0u8;
                let mut byte_idx = 0usize;
                while byte_idx < bytes.len() {
                    if (bytes[byte_idx] >> bit_in_byte) & 1 == 1 {
                        result = small_mul(result, base, p);
                    }
                    bit_in_byte += 1;
                    if bit_in_byte == 8 {
                        bit_in_byte = 0;
                        byte_idx += 1;
                    }
                    base = small_mul(base, base, p);
                }
                FieldElem::from_u64_unchecked(result)
            }
        }
    }

    /// Modular exponentiation by a `u64` exponent.
    pub fn pow_u64(&self, a: &FieldElem, exp: u64) -> FieldElem {
        if exp == 0 {
            return self.one();
        }
        match &self.kind {
            FieldKind::Gmp { prime, .. } => {
                let exp_int = Integer::from(exp);
                let mut out = Integer::new();
                out.assign(a.as_gmp().pow_mod_ref(&exp_int, prime).unwrap());
                FieldElem::from_integer_unchecked(out)
            }
            FieldKind::Small { prime } => {
                FieldElem::from_u64_unchecked(small_pow(a.as_small(), exp, *prime))
            }
        }
    }

    /// Clone an element. Equivalent to `a.clone()`; named for
    /// compatibility with the feanor `RingBase`-style API.
    #[inline]
    pub fn clone_el(&self, a: &FieldElem) -> FieldElem {
        a.clone()
    }

    // ---- feanor-math `RingBase`-style aliases ----
    // Forward to the canonical methods (`eq`, `neg`, `mul`, `add`,
    // `sub`, `from_i64`, `.clone()`). Retained for callers that
    // expect the feanor naming.

    #[inline]
    pub fn eq_el(&self, a: &FieldElem, b: &FieldElem) -> bool {
        a == b
    }

    /// Negate by-value (feanor-style: consumes input). Equivalent to `neg(&a)`.
    #[inline]
    pub fn negate(&self, a: FieldElem) -> FieldElem {
        self.neg(&a)
    }

    #[inline]
    pub fn mul_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.mul(a, b)
    }

    #[inline]
    pub fn add_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.add(a, b)
    }

    #[inline]
    pub fn sub_ref(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        self.sub(a, b)
    }

    #[inline]
    pub fn from_int(&self, n: i64) -> FieldElem {
        self.from_i64(n)
    }

    #[inline]
    pub fn int_hom(&self) -> IntHom<'_> {
        IntHom { field: self }
    }
}

use rug::Assign;

// ──────────────────────────── Small-prime arithmetic ────────────────────

#[inline(always)]
fn small_add(a: u64, b: u64, p: u64) -> u64 {
    // `a, b < p <= u64::MAX`. `a + b` may overflow u64 only when
    // `p > u64::MAX / 2`. Use a 128-bit intermediate so the wraparound
    // case is correct for the full u64 prime range.
    let s = (a as u128) + (b as u128);
    let p128 = p as u128;
    if s >= p128 { (s - p128) as u64 } else { s as u64 }
}

#[inline(always)]
fn small_sub(a: u64, b: u64, p: u64) -> u64 {
    if a >= b { a - b } else { p - (b - a) }
}

#[inline(always)]
fn small_mul(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128) * (b as u128) % (p as u128)) as u64
}

#[inline(always)]
fn small_neg(a: u64, p: u64) -> u64 {
    if a == 0 { 0 } else { p - a }
}

/// Multiplicative inverse via the extended Euclidean algorithm in
/// signed 128-bit. Returns `None` when `a == 0`, or when
/// `gcd(a, p) != 1` (cannot occur for a prime `p` and nonzero `a`;
/// the check keeps the function total).
fn small_inv(a: u64, p: u64) -> Option<u64> {
    if a == 0 {
        return None;
    }
    let p_i = p as i128;
    let (mut r0, mut r1) = (p_i, a as i128);
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        let new_r = r0 - q * r1;
        r0 = r1;
        r1 = new_r;
        let new_s = s0 - q * s1;
        s0 = s1;
        s1 = new_s;
    }
    if r0 != 1 && r0 != -1 {
        return None;
    }
    // s0 is the inverse (possibly negative or oversized); reduce mod p.
    let inv = if r0 == -1 { (-s0).rem_euclid(p_i) } else { s0.rem_euclid(p_i) };
    Some(inv as u64)
}

/// Modular exponentiation by repeated squaring.
fn small_pow(mut base: u64, mut exp: u64, p: u64) -> u64 {
    let mut result: u64 = 1;
    base %= p;
    while exp > 0 {
        if exp & 1 == 1 {
            result = small_mul(result, base, p);
        }
        exp >>= 1;
        if exp > 0 {
            base = small_mul(base, base, p);
        }
    }
    result
}

// ──────────────────────────── Misc helpers ──────────────────────────────

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
        Arc::ptr_eq(&self.prime_bu, &other.prime_bu) || *self.prime_bu == *other.prime_bu
    }
}
impl Eq for PrimeField {}

// ─────────────────────────────── Tests ──────────────────────────────────

#[cfg(test)]
mod tests;
