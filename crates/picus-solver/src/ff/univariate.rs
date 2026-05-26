//! Univariate polynomial arithmetic and root finding over GF(p).
//!
//! Replaces `feanor_math::dense_poly` + `FactorPolyField` for the single use case
//! of finding roots of polynomials over GF(p) (used by the model construction in
//! the SMT layer for branching). The root-finding algorithm is Cantor–Zassenhaus
//! with squarefree decomposition, specialised for GF(p).

use num_bigint::BigUint;
use num_traits::{One, Zero};
use oorandom::Rand64;

use super::field::{FieldElem, PrimeField};

/// A univariate polynomial over GF(p). Coefficients are stored low-to-high
/// (`coeffs[i]` is the coefficient of `x^i`); trailing zero coefficients are
/// stripped so `coeffs.last()` is always non-zero (or the vector is empty for
/// the zero polynomial).
#[derive(Clone, Debug)]
pub struct UnivariatePoly {
    coeffs: Vec<FieldElem>,
}

impl UnivariatePoly {
    pub fn zero() -> Self {
        UnivariatePoly { coeffs: Vec::new() }
    }

    pub fn one(field: &PrimeField) -> Self {
        UnivariatePoly { coeffs: vec![field.one()] }
    }

    /// Build from a list of coefficients (low-to-high). Trailing zeros are
    /// trimmed so the leading coefficient (if any) is non-zero.
    pub fn from_coeffs(mut coeffs: Vec<FieldElem>, field: &PrimeField) -> Self {
        while coeffs.last().map_or(false, |c| field.is_zero(c)) {
            coeffs.pop();
        }
        UnivariatePoly { coeffs }
    }

    pub fn coeffs(&self) -> &[FieldElem] {
        &self.coeffs
    }

    /// Degree of the polynomial; `None` for the zero polynomial.
    pub fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() { None } else { Some(self.coeffs.len() - 1) }
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Leading coefficient (None for the zero polynomial).
    pub fn leading_coefficient(&self) -> Option<&FieldElem> {
        self.coeffs.last()
    }

    pub fn evaluate(&self, x: &FieldElem, field: &PrimeField) -> FieldElem {
        // Horner's rule.
        let mut acc = field.zero();
        for c in self.coeffs.iter().rev() {
            acc = field.mul(&acc, x);
            acc = field.add(&acc, c);
        }
        acc
    }

    pub fn add(&self, other: &Self, field: &PrimeField) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let a = self.coeffs.get(i);
            let b = other.coeffs.get(i);
            let v = match (a, b) {
                (Some(x), Some(y)) => field.add(x, y),
                (Some(x), None) => field.clone_el(x),
                (None, Some(y)) => field.clone_el(y),
                (None, None) => field.zero(),
            };
            out.push(v);
        }
        UnivariatePoly::from_coeffs(out, field)
    }

    pub fn sub(&self, other: &Self, field: &PrimeField) -> Self {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let a = self.coeffs.get(i);
            let b = other.coeffs.get(i);
            let v = match (a, b) {
                (Some(x), Some(y)) => field.sub(x, y),
                (Some(x), None) => field.clone_el(x),
                (None, Some(y)) => field.neg(y),
                (None, None) => field.zero(),
            };
            out.push(v);
        }
        UnivariatePoly::from_coeffs(out, field)
    }

    pub fn neg(&self, field: &PrimeField) -> Self {
        let coeffs = self.coeffs.iter().map(|c| field.neg(c)).collect();
        UnivariatePoly { coeffs }
    }

    pub fn mul(&self, other: &Self, field: &PrimeField) -> Self {
        if self.is_zero() || other.is_zero() {
            return UnivariatePoly::zero();
        }
        let n = self.coeffs.len() + other.coeffs.len() - 1;
        let mut out: Vec<FieldElem> = (0..n).map(|_| field.zero()).collect();
        for (i, a) in self.coeffs.iter().enumerate() {
            if field.is_zero(a) { continue; }
            for (j, b) in other.coeffs.iter().enumerate() {
                if field.is_zero(b) { continue; }
                let prod = field.mul(a, b);
                let acc = field.add(&out[i + j], &prod);
                out[i + j] = acc;
            }
        }
        UnivariatePoly::from_coeffs(out, field)
    }

    pub fn scale(&self, c: &FieldElem, field: &PrimeField) -> Self {
        if field.is_zero(c) || self.is_zero() {
            return UnivariatePoly::zero();
        }
        let coeffs = self.coeffs.iter().map(|a| field.mul(a, c)).collect();
        UnivariatePoly { coeffs }
    }

    /// Polynomial long division: returns `(q, r)` such that `self = q * other + r`
    /// with `deg(r) < deg(other)`. Panics if `other` is zero.
    pub fn div_rem(&self, other: &Self, field: &PrimeField) -> (Self, Self) {
        assert!(!other.is_zero(), "division by zero polynomial");
        if self.degree() < other.degree() {
            return (UnivariatePoly::zero(), self.clone());
        }
        let lc_other = other.leading_coefficient().unwrap();
        let lc_other_inv = field
            .inv(lc_other)
            .expect("leading coefficient of divisor must be invertible in a field");
        let mut rem = self.clone();
        let n = self.degree().unwrap();
        let m = other.degree().unwrap();
        let mut q_coeffs: Vec<FieldElem> = (0..=n - m).map(|_| field.zero()).collect();
        while rem.degree().map_or(false, |d| d >= m) {
            let d = rem.degree().unwrap();
            let lc_rem = rem.leading_coefficient().unwrap();
            let factor = field.mul(lc_rem, &lc_other_inv);
            let shift = d - m;
            q_coeffs[shift] = field.add(&q_coeffs[shift], &factor);
            // rem -= factor * x^shift * other
            for (j, b) in other.coeffs.iter().enumerate() {
                if field.is_zero(b) { continue; }
                let prod = field.mul(&factor, b);
                let idx = shift + j;
                let new = field.sub(&rem.coeffs[idx], &prod);
                rem.coeffs[idx] = new;
            }
            // Trim leading zeros from rem.
            while rem.coeffs.last().map_or(false, |c| field.is_zero(c)) {
                rem.coeffs.pop();
            }
        }
        let q = UnivariatePoly::from_coeffs(q_coeffs, field);
        (q, rem)
    }

    pub fn rem(&self, other: &Self, field: &PrimeField) -> Self {
        self.div_rem(other, field).1
    }

    /// Monic GCD of `self` and `other` (Euclidean algorithm).
    pub fn gcd(&self, other: &Self, field: &PrimeField) -> Self {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b, field);
            a = b;
            b = r;
        }
        if a.is_zero() { a } else { a.make_monic(field) }
    }

    pub fn make_monic(&self, field: &PrimeField) -> Self {
        if self.is_zero() {
            return UnivariatePoly::zero();
        }
        let lc = self.leading_coefficient().unwrap();
        if field.is_one(lc) {
            return self.clone();
        }
        let inv = field.inv(lc).expect("leading coefficient invertible in field");
        self.scale(&inv, field)
    }

    /// Formal derivative.
    pub fn derivative(&self, field: &PrimeField) -> Self {
        if self.coeffs.len() <= 1 {
            return UnivariatePoly::zero();
        }
        let mut out = Vec::with_capacity(self.coeffs.len() - 1);
        for i in 1..self.coeffs.len() {
            let mult = field.from_u64(i as u64);
            out.push(field.mul(&self.coeffs[i], &mult));
        }
        UnivariatePoly::from_coeffs(out, field)
    }

    /// Compute `self^exp mod modulus` using square-and-multiply.
    pub fn pow_mod(&self, exp: &BigUint, modulus: &Self, field: &PrimeField) -> Self {
        let one = UnivariatePoly::one(field);
        if exp.is_zero() {
            return one.rem(modulus, field);
        }
        let mut result = one;
        let base = self.rem(modulus, field);
        // Iterate bits from MSB to LSB.
        let bits = exp.bits();
        for i in (0..bits).rev() {
            result = result.mul(&result, field).rem(modulus, field);
            if exp.bit(i) {
                result = result.mul(&base, field).rem(modulus, field);
            }
        }
        result
    }
}

impl UnivariatePoly {
    /// `x` as a polynomial.
    fn x(field: &PrimeField) -> Self {
        UnivariatePoly { coeffs: vec![field.zero(), field.one()] }
    }
}

/// Squarefree part: `f / gcd(f, f')`.
fn squarefree(poly: &UnivariatePoly, field: &PrimeField) -> UnivariatePoly {
    if poly.is_zero() {
        return UnivariatePoly::zero();
    }
    let d = poly.derivative(field);
    if d.is_zero() {
        // f' = 0: in characteristic p, f is a polynomial in x^p; for our use
        // case (single squarefree decomposition before root extraction) we
        // simply return f itself — Cantor–Zassenhaus will still find linear
        // factors via `x^p - x`.
        return poly.make_monic(field);
    }
    let g = poly.gcd(&d, field);
    poly.div_rem(&g, field).0.make_monic(field)
}

/// Extract the product of all distinct linear factors of `poly` by computing
/// `gcd(poly, x^p - x)`.
fn distinct_linear_part(poly: &UnivariatePoly, field: &PrimeField) -> UnivariatePoly {
    // Compute x^p mod poly, then subtract x, then gcd with poly.
    let x_poly = UnivariatePoly::x(field);
    let xp = x_poly.pow_mod(field.prime(), poly, field);
    let xp_minus_x = xp.sub(&x_poly, field);
    poly.gcd(&xp_minus_x, field)
}

/// Generate a uniformly-random BigUint in [0, bound) using `Rand64`.
fn rand_below(rng: &mut Rand64, bound: &BigUint) -> BigUint {
    // Build a candidate of the same bit length and reject if >= bound.
    let bits = bound.bits();
    if bits == 0 {
        return BigUint::from(0u32);
    }
    let n_u64 = ((bits + 63) / 64) as usize;
    loop {
        let mut digits = Vec::with_capacity(n_u64);
        for _ in 0..n_u64 {
            digits.push(rng.rand_u64());
        }
        // Mask the top word to avoid wasted rejections.
        let extra_bits = (n_u64 as u64) * 64 - bits;
        if extra_bits > 0 {
            let last = digits.last_mut().unwrap();
            *last &= u64::MAX >> extra_bits;
        }
        let v = BigUint::from_slice(
            &digits
                .iter()
                .flat_map(|w| [(*w as u32), (*w >> 32) as u32])
                .collect::<Vec<u32>>(),
        );
        if &v < bound {
            return v;
        }
    }
}

/// Cantor–Zassenhaus equal-degree factorization for `poly`, which is assumed
/// to be the product of distinct linear factors over GF(p) (i.e. `poly` divides
/// `x^p - x`). Splits `poly` recursively until each factor is linear, then
/// returns the list of linear factors.
fn split_linear_factors(
    poly: &UnivariatePoly,
    field: &PrimeField,
    rng: &mut Rand64,
) -> Vec<UnivariatePoly> {
    let mut out = Vec::new();
    let mut stack = vec![poly.clone()];
    let p = field.prime().clone();
    let two = BigUint::from(2u32);
    if p < two {
        // `p < 2` is not a field; `PrimeField::new` rejects this case.
        return vec![poly.clone()];
    }
    let exp = (&p - BigUint::one()) / &two;

    while let Some(g) = stack.pop() {
        let deg = g.degree().unwrap_or(0);
        if deg == 0 {
            continue;
        }
        if deg == 1 {
            out.push(g.make_monic(field));
            continue;
        }
        // p == 2: the standard splitting `gcd(g, x^((p-1)/2) - 1)` is
        // ill-defined. Enumerate `c ∈ {0, 1}` directly.
        if p == two {
            let mut found = Vec::new();
            for c in 0u64..2 {
                let v = field.from_u64(c);
                if field.is_zero(&g.evaluate(&v, field)) {
                    let mut linear = UnivariatePoly::from_coeffs(
                        vec![field.neg(&v), field.one()],
                        field,
                    );
                    linear = linear.make_monic(field);
                    found.push(linear);
                }
            }
            out.extend(found);
            continue;
        }
        // Random splitting: pick `a`, compute h = (x + a)^exp - 1 mod g.
        let mut split = None;
        for _attempt in 0..40 {
            let a_big = rand_below(rng, &p);
            let a = field.from_biguint(&a_big);
            let x_plus_a = UnivariatePoly::from_coeffs(vec![a, field.one()], field);
            let h = x_plus_a.pow_mod(&exp, &g, field);
            let h_minus_1 = h.sub(&UnivariatePoly::one(field), field);
            let factor = g.gcd(&h_minus_1, field);
            let fdeg = factor.degree().unwrap_or(0);
            if fdeg > 0 && fdeg < deg {
                let other = g.div_rem(&factor, field).0;
                split = Some((factor, other));
                break;
            }
        }
        match split {
            Some((a, b)) => {
                stack.push(a);
                stack.push(b);
            }
            None => {
                // Distinct-degree split exhausted the retry budget;
                // return the unsplit polynomial as a single factor.
                out.push(g);
            }
        }
    }
    out
}

/// Cantor–Zassenhaus for the squarefree polynomial `poly`. Returns its
/// irreducible factors (over GF(p), restricted to those involved in the
/// linear part — non-linear irreducible factors are returned as a single
/// composite polynomial since we only care about roots).
pub(crate) fn cantor_zassenhaus(
    poly: &UnivariatePoly,
    field: &PrimeField,
) -> Vec<UnivariatePoly> {
    let linear_product = distinct_linear_part(poly, field);
    if linear_product.degree().unwrap_or(0) == 0 {
        return Vec::new();
    }
    // Deterministic seed for reproducibility; root-finding correctness does
    // not depend on randomness, only its probability per attempt.
    let mut rng = Rand64::new(0xC0FFEE_DEADBEEFu128);
    split_linear_factors(&linear_product, field, &mut rng)
}

/// Find all roots of `poly` in GF(p). Returns an empty vector if `poly` is
/// the zero polynomial (every element is a root, which is not a useful
/// answer; callers should check for the zero case themselves).
pub fn find_roots(poly: &UnivariatePoly, field: &PrimeField) -> Vec<FieldElem> {
    find_roots_checked(poly, field).0
}

/// Like [`find_roots`], but also reports whether root finding was
/// **complete**. Returns `(roots, complete)`:
///
/// * `complete == true` — every root of `poly` in GF(p) is present in
///   `roots`.
/// * `complete == false` — Cantor–Zassenhaus could not fully split a
///   product of linear factors within its randomised retry budget, so
///   `roots` is a (possibly empty) *subset* of the true root set.
///
/// A caller that uses an exhausted/empty root set to prove a branch
/// infeasible MUST consult this flag: on `complete == false` it must not
/// treat the enumeration as exhaustive, since a dropped root could be the
/// satisfying assignment — concluding UNSAT there would be unsound. Such
/// callers should fall back to a non-exhaustive search (yielding Unknown)
/// instead.
pub fn find_roots_checked(poly: &UnivariatePoly, field: &PrimeField) -> (Vec<FieldElem>, bool) {
    if poly.is_zero() {
        return (Vec::new(), true);
    }
    let deg = poly.degree().unwrap_or(0);
    if deg == 0 {
        return (Vec::new(), true);
    }
    if deg == 1 {
        // a*x + b = 0 -> x = -b / a
        let a = &poly.coeffs[1];
        let b = &poly.coeffs[0];
        let neg_b = field.neg(b);
        let inv_a = field.inv(a).expect("non-zero leading coefficient");
        return (vec![field.mul(&neg_b, &inv_a)], true);
    }
    let monic = poly.make_monic(field);
    let sf = squarefree(&monic, field);
    let factors = cantor_zassenhaus(&sf, field);
    let mut roots = Vec::with_capacity(factors.len());
    let mut complete = true;
    for f in factors {
        match f.degree() {
            // Each linear factor is monic: x - r, so r = -f.coeffs[0].
            Some(1) => roots.push(field.neg(&f.coeffs[0])),
            // `cantor_zassenhaus` already stripped the non-linear (rootless)
            // part via `distinct_linear_part`, so any degree >= 2 factor here
            // is an *unsplit product of linear factors* — its roots exist in
            // GF(p) but were not extracted within the retry budget.
            Some(d) if d >= 2 => complete = false,
            _ => {}
        }
    }
    // Sort by canonical `BigUint` value for deterministic output.
    roots.sort_by(|a, b| a.as_biguint().cmp(&b.as_biguint()));
    roots.dedup_by(|a, b| field.eq(a, b));
    (roots, complete)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn small_field() -> PrimeField {
        PrimeField::new(BigUint::from(101u32))
    }

    fn bn128_field() -> PrimeField {
        let p_str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
        PrimeField::new(p_str.parse::<BigUint>().unwrap())
    }

    fn poly_from_ints(coeffs: &[i64], f: &PrimeField) -> UnivariatePoly {
        let cs = coeffs.iter().map(|&c| f.from_i64(c)).collect();
        UnivariatePoly::from_coeffs(cs, f)
    }

    /// Ground-truth roots: evaluate at every element of GF(p) (small p only).
    fn brute_roots(p: &UnivariatePoly, f: &PrimeField) -> Vec<BigUint> {
        let prime = f.prime().clone();
        let mut out = Vec::new();
        let mut c = BigUint::from(0u32);
        while c < prime {
            if f.is_zero(&p.evaluate(&f.from_biguint(&c), f)) {
                out.push(c.clone());
            }
            c += 1u32;
        }
        out
    }

    #[test]
    fn find_roots_checked_matches_brute_force_and_is_complete() {
        let f = small_field();
        let lin = |r: i64| poly_from_ints(&[-r, 1], &f); // x - r

        // (x-3)(x-7)(x-50) — distinct roots.
        let p1 = lin(3).mul(&lin(7), &f).mul(&lin(50), &f);
        // (x-4)^2 (x-9) — repeated root 4 (deduped) plus 9.
        let p2 = lin(4).mul(&lin(4), &f).mul(&lin(9), &f);
        // x^2 - 2 — no root in GF(101) (2 is a non-residue).
        let p3 = poly_from_ints(&[-2, 0, 1], &f);
        // Nonzero constant — no roots.
        let p4 = poly_from_ints(&[5], &f);

        for p in [&p1, &p2, &p3, &p4] {
            let (roots, complete) = find_roots_checked(p, &f);
            assert!(complete, "small-prime root finding must report complete");
            let mut got: Vec<BigUint> = roots.iter().map(|r| r.as_biguint().clone()).collect();
            got.sort();
            let mut want = brute_roots(p, &f);
            want.sort();
            assert_eq!(got, want, "checked roots must match brute force");
            // `find_roots` is exactly the `.0` projection.
            let mut plain: Vec<BigUint> =
                find_roots(p, &f).iter().map(|r| r.as_biguint().clone()).collect();
            plain.sort();
            assert_eq!(plain, got, "find_roots must equal find_roots_checked.0");
        }
    }

    #[test]
    fn evaluate_horner() {
        let f = small_field();
        // p(x) = 2x^2 + 3x + 1
        let p = poly_from_ints(&[1, 3, 2], &f);
        // p(5) = 50 + 15 + 1 = 66
        let v = p.evaluate(&f.from_u64(5), &f);
        assert_eq!(v.as_biguint(), BigUint::from(66u32));
    }

    #[test]
    fn add_sub_mul() {
        let f = small_field();
        let a = poly_from_ints(&[1, 2, 3], &f); // 3x^2 + 2x + 1
        let b = poly_from_ints(&[4, 5], &f);    // 5x + 4
        let s = a.add(&b, &f);
        // (3x^2 + 2x + 1) + (5x + 4) = 3x^2 + 7x + 5
        assert_eq!(s.coeffs[0].as_biguint(), BigUint::from(5u32));
        assert_eq!(s.coeffs[1].as_biguint(), BigUint::from(7u32));
        assert_eq!(s.coeffs[2].as_biguint(), BigUint::from(3u32));
        let d = a.sub(&b, &f);
        // (3x^2 + 2x + 1) - (5x + 4) = 3x^2 - 3x - 3 = 3x^2 + 98x + 98 mod 101
        assert_eq!(d.coeffs[0].as_biguint(), BigUint::from(98u32));
        assert_eq!(d.coeffs[1].as_biguint(), BigUint::from(98u32));
        assert_eq!(d.coeffs[2].as_biguint(), BigUint::from(3u32));
        let m = a.mul(&b, &f);
        // (3x^2 + 2x + 1) * (5x + 4) = 15x^3 + 12x^2 + 10x^2 + 8x + 5x + 4
        //                           = 15x^3 + 22x^2 + 13x + 4
        assert_eq!(m.coeffs[0].as_biguint(), BigUint::from(4u32));
        assert_eq!(m.coeffs[1].as_biguint(), BigUint::from(13u32));
        assert_eq!(m.coeffs[2].as_biguint(), BigUint::from(22u32));
        assert_eq!(m.coeffs[3].as_biguint(), BigUint::from(15u32));
    }

    #[test]
    fn div_rem_basic() {
        let f = small_field();
        // (x^3 - 1) / (x - 1) = x^2 + x + 1
        let num = poly_from_ints(&[-1, 0, 0, 1], &f);
        let den = poly_from_ints(&[-1, 1], &f);
        let (q, r) = num.div_rem(&den, &f);
        assert!(r.is_zero());
        assert_eq!(q.coeffs.len(), 3);
        assert_eq!(q.coeffs[0].as_biguint(), BigUint::from(1u32));
        assert_eq!(q.coeffs[1].as_biguint(), BigUint::from(1u32));
        assert_eq!(q.coeffs[2].as_biguint(), BigUint::from(1u32));
    }

    #[test]
    fn gcd_works() {
        let f = small_field();
        // gcd(x^2 - 1, x - 1) = x - 1 (monic)
        let a = poly_from_ints(&[-1, 0, 1], &f);
        let b = poly_from_ints(&[-1, 1], &f);
        let g = a.gcd(&b, &f);
        assert_eq!(g.degree(), Some(1));
        assert_eq!(g.leading_coefficient().unwrap().as_biguint(), BigUint::from(1u32));
        // Should be (x - 1).
        assert_eq!(g.coeffs[0].as_biguint(), BigUint::from(100u32)); // -1 mod 101
    }

    #[test]
    fn pow_mod_works() {
        let f = small_field();
        // x^5 mod (x^2 - 1) over GF(101).
        // x^2 = 1, so x^5 = x.
        let x = UnivariatePoly::x(&f);
        let modulus = poly_from_ints(&[-1, 0, 1], &f);
        let r = x.pow_mod(&BigUint::from(5u32), &modulus, &f);
        assert_eq!(r.degree(), Some(1));
        assert_eq!(r.coeffs[0].as_biguint(), BigUint::from(0u32));
        assert_eq!(r.coeffs[1].as_biguint(), BigUint::from(1u32));
    }

    #[test]
    fn find_roots_quadratic_small() {
        let f = small_field();
        // (x - 3)(x - 7) = x^2 - 10x + 21
        let p = poly_from_ints(&[21, -10, 1], &f);
        let mut roots: Vec<u64> = find_roots(&p, &f)
            .iter()
            .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
            .collect();
        roots.sort();
        assert_eq!(roots, vec![3u64, 7u64]);
    }

    #[test]
    fn find_roots_no_roots() {
        let f = small_field();
        // x^2 + 1 over GF(101): -1 is a QR iff 101 ≡ 1 mod 4. 101 mod 4 = 1, so it has roots.
        // Use x^2 + 2 instead. Check: -2 is QR iff (-2 | 101) = (-1|101)*(2|101) = 1 * 1 = 1. Has roots.
        // Use a polynomial with no roots: pick (x^2 + a) where a is a non-QR.
        // Compute a non-QR by finding b with b^((p-1)/2) = -1.
        let mut nonqr = None;
        for cand in 2u64..50 {
            let v = f.from_u64(cand);
            let exp = (BigUint::from(101u32) - BigUint::one()) / BigUint::from(2u32);
            let pw = f.pow(&v, &exp);
            if pw.as_biguint() == (BigUint::from(101u32) - BigUint::one()) {
                nonqr = Some(cand);
                break;
            }
        }
        let nq = nonqr.expect("non-QR exists in GF(101)");
        // p(x) = x^2 + nq has no roots (since -nq is also a non-QR? actually we need -nq to be a non-QR;
        // sufficient: choose nq so that -nq is a non-QR. With p % 4 == 1, -1 is a QR, so -nq is QR iff
        // nq is QR — so -nq is non-QR. Good.).
        let p = poly_from_ints(&[nq as i64, 0, 1], &f);
        let roots = find_roots(&p, &f);
        assert!(roots.is_empty(), "expected no roots, got {:?}", roots.iter().map(|r| r.as_biguint().clone()).collect::<Vec<_>>());
    }

    #[test]
    fn find_roots_cubic_small() {
        let f = small_field();
        // (x - 1)(x - 2)(x - 3) = x^3 - 6x^2 + 11x - 6
        let p = poly_from_ints(&[-6, 11, -6, 1], &f);
        let mut roots: Vec<u64> = find_roots(&p, &f)
            .iter()
            .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
            .collect();
        roots.sort();
        assert_eq!(roots, vec![1, 2, 3]);
    }

    #[test]
    fn find_roots_with_multiplicity() {
        let f = small_field();
        // (x - 5)^2 = x^2 - 10x + 25
        let p = poly_from_ints(&[25, -10, 1], &f);
        let roots: Vec<u64> = find_roots(&p, &f)
            .iter()
            .map(|r| r.as_biguint().iter_u64_digits().next().unwrap_or(0))
            .collect();
        assert_eq!(roots, vec![5]); // dedup'd
    }

    #[test]
    fn find_roots_linear() {
        let f = small_field();
        // 3x - 6 -> x = 2.
        let p = poly_from_ints(&[-6, 3], &f);
        let roots = find_roots(&p, &f);
        assert_eq!(roots.len(), 1);
        assert_eq!(roots[0].as_biguint(), BigUint::from(2u32));
    }

    #[test]
    fn find_roots_bn128() {
        let f = bn128_field();
        // (x - 5)(x - 7) = x^2 - 12x + 35
        let p = poly_from_ints(&[35, -12, 1], &f);
        let mut roots: Vec<BigUint> = find_roots(&p, &f).iter().map(|r| r.as_biguint().clone()).collect();
        roots.sort();
        assert_eq!(roots, vec![BigUint::from(5u32), BigUint::from(7u32)]);
    }

    #[test]
    fn find_roots_zero_poly() {
        let f = small_field();
        let p = UnivariatePoly::zero();
        assert!(find_roots(&p, &f).is_empty());
    }

    #[test]
    fn find_roots_constant_poly() {
        let f = small_field();
        let p = poly_from_ints(&[7], &f);
        assert!(find_roots(&p, &f).is_empty());
    }
}
