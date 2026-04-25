//! Univariate root finding over GF(p).
//!
//! Matches cvc5's `uni_roots.cpp`:
//! - Small fields: delegate to feanor-math's Cantor-Zassenhaus factoring.
//! - Large fields: squarefree preprocessing via `distinctRootsPoly`
//!   (gcd with x^q - x mod f), then Berlekamp-Rabin splitting.

use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::*;
use feanor_math::rings::poly::*;
use feanor_math::algorithms::poly_factor::FactorPolyField;
use feanor_math::field::FieldStore;
use feanor_math::pid::EuclideanRingStore;

use crate::field::{FfField, FfEl};

/// Find all roots of a univariate polynomial over GF(p).
///
/// `coeffs[i]` is the coefficient of x^i.
///
/// Matches cvc5's `roots()` in `uni_roots.cpp`:
/// 1. Fast path for zero polynomial, constant, and linear.
/// 2. Squarefree preprocessing: `gcd(f, x^q - x mod f)` isolates the
///    product of distinct linear factors.
/// 3. Factoring of the squarefree part via Cantor-Zassenhaus.
pub fn find_roots(field: &FfField, coeffs: &[FfEl]) -> Vec<FfEl> {
    let _t = crate::profile::ScopedTimer::new("find_roots");
    let fp = field.field();
    let poly_ring = DensePolyRing::new(fp, "t");

    // Build polynomial from coefficients
    let poly = poly_ring.from_terms(
        coeffs.iter().enumerate().map(|(i, c)| (fp.clone_el(c), i))
    );

    if poly_ring.is_zero(&poly) {
        return vec![];
    }

    // Fast path: constant polynomial (degree 0) → no roots
    let deg = match poly_ring.degree(&poly) {
        Some(d) => d,
        None => return vec![],
    };
    if deg == 0 {
        return vec![];
    }

    // Fast path: linear polynomial → root = -c0/c1
    // Matches cvc5's uni_roots.cpp:184-188
    if deg == 1 {
        let c0 = poly_ring.coefficient_at(&poly, 0);
        let c1 = poly_ring.coefficient_at(&poly, 1);
        let root = fp.negate(fp.div(&c0, &c1));
        return vec![root];
    }

    // Squarefree preprocessing: compute gcd(f, x^q - x mod f) to isolate
    // the product of distinct linear factors.  This strips repeated roots
    // and irreducible factors of degree > 1.
    // Matches cvc5's `distinctRootsPoly` (uni_roots.cpp:74-85).
    let x = poly_ring.indeterminate();
    let xq_mod_f = power_mod_poly(&poly_ring, &x, &field.prime, &poly);
    let field_poly = poly_ring.sub(xq_mod_f, poly_ring.clone_el(&x));
    let distinct_poly = poly_gcd_impl(&poly_ring, &poly, &field_poly);

    let _distinct_deg = match poly_ring.degree(&distinct_poly) {
        Some(d) if d >= 1 => d,
        _ => return vec![], // no linear factors
    };

    // After squarefree preprocessing, use cvc5-style extraction:
    // zero root fast path, linear fast path, then factor.
    // Matches cvc5's Rabin loop (uni_roots.cpp:168-217).
    let mut roots = Vec::new();
    let mut to_factor = vec![distinct_poly];

    while let Some(p) = to_factor.pop() {
        let d = match poly_ring.degree(&p) {
            Some(d) => d,
            None => continue,
        };
        if d == 0 {
            // Constant — no roots
            continue;
        }
        let c0 = poly_ring.coefficient_at(&p, 0);
        if fp.is_zero(&c0) {
            // Zero root: extract and divide by x
            roots.push(fp.zero());
            let shifted = poly_ring.from_terms(
                (1..=d).map(|i| (fp.clone_el(poly_ring.coefficient_at(&p, i)), i - 1))
            );
            to_factor.push(shifted);
        } else if d == 1 {
            // Linear: direct root extraction
            let c1 = poly_ring.coefficient_at(&p, 1);
            roots.push(fp.negate(fp.div(&c0, &c1)));
        } else {
            // Factor via library (already squarefree, only linear factors)
            let (factors, _unit) = <_ as FactorPolyField>::factor_poly(&poly_ring, &p);
            for (f, _mult) in factors {
                if poly_ring.degree(&f) == Some(1) {
                    let fc0 = poly_ring.coefficient_at(&f, 0);
                    let fc1 = poly_ring.coefficient_at(&f, 1);
                    roots.push(fp.negate(fp.div(&fc0, &fc1)));
                }
            }
        }
    }

    roots
}

/// Compute b^e mod m in a polynomial ring using repeated squaring.
/// Matches cvc5's `powerMod` (uni_roots.cpp:56-72).
fn power_mod_poly<P: RingStore + Copy>(
    poly_ring: P,
    b: &El<P>,
    e: &num_bigint::BigUint,
    m: &El<P>,
) -> El<P>
where
    P::Type: PolyRing,
    <P::Type as RingExtension>::BaseRing: FieldStore,
    <<P::Type as RingExtension>::BaseRing as RingStore>::Type: feanor_math::field::Field,
    P: EuclideanRingStore,
    P::Type: feanor_math::pid::EuclideanRing,
{
    use num_traits::Zero;

    let mut acc = poly_ring.one();
    let mut b_power = poly_ring.clone_el(b);
    let mut exp = e.clone();

    while !exp.is_zero() {
        if &exp % 2u32 == num_bigint::BigUint::from(1u32) {
            acc = poly_ring.mul(acc, poly_ring.clone_el(&b_power));
            let (_, r) = poly_ring.euclidean_div_rem(acc, m);
            acc = r;
        }
        b_power = poly_ring.mul(
            poly_ring.clone_el(&b_power),
            poly_ring.clone_el(&b_power),
        );
        let (_, r) = poly_ring.euclidean_div_rem(b_power, m);
        b_power = r;
        exp >>= 1;
    }

    acc
}

/// Polynomial GCD via Euclidean algorithm.
fn poly_gcd_impl<P: RingStore + Copy>(
    poly_ring: P,
    a: &El<P>,
    b: &El<P>,
) -> El<P>
where
    P::Type: PolyRing,
    P: EuclideanRingStore,
    P::Type: feanor_math::pid::EuclideanRing,
{
    let mut x = poly_ring.clone_el(a);
    let mut y = poly_ring.clone_el(b);

    while !poly_ring.is_zero(&y) {
        let (_, r) = poly_ring.euclidean_div_rem(x, &y);
        x = y;
        y = r;
    }

    x
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_roots_linear() {
        // x - 3 = 0 over GF(17) → root = 3
        let ff = FfField::new(&BigUint::from(17u32));

        let coeffs = vec![
            ff.from_biguint(&BigUint::from(14u32)), // -3 mod 17
            ff.one(),
        ];

        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 1);
        assert_eq!(ff.to_biguint(&roots[0]), BigUint::from(3u32));
    }

    #[test]
    fn test_roots_quadratic() {
        // x^2 - 1 = 0 over GF(17) → roots 1, 16
        let ff = FfField::new(&BigUint::from(17u32));

        let coeffs = vec![
            ff.from_biguint(&BigUint::from(16u32)), // -1 mod 17
            ff.zero(),
            ff.one(),
        ];

        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 2);
        let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
        vals.sort();
        assert_eq!(vals, vec![BigUint::from(1u32), BigUint::from(16u32)]);
    }

    #[test]
    fn test_no_roots() {
        // x^2 + 1 = 0 over GF(3) → no roots
        let ff = FfField::new(&BigUint::from(3u32));

        let coeffs = vec![ff.one(), ff.zero(), ff.one()];
        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 0);
    }

    #[test]
    fn test_roots_with_zero_root() {
        // x^2 - x = 0 over GF(7) → roots 0, 1
        let ff = FfField::new(&BigUint::from(7u32));
        let coeffs = vec![ff.zero(), ff.from_biguint(&BigUint::from(6u32)), ff.one()];
        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 2);
        let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
        vals.sort();
        assert_eq!(vals, vec![BigUint::from(0u32), BigUint::from(1u32)]);
    }

    #[test]
    fn test_roots_high_degree_with_irreducible_factors() {
        // x^4 - 1 over GF(5): by Fermat's little theorem, a^4 ≡ 1 mod 5
        // for all a ∈ {1,2,3,4}, so all four non-zero elements are roots.
        let ff = FfField::new(&BigUint::from(5u32));
        let coeffs = vec![
            ff.from_biguint(&BigUint::from(4u32)), // -1
            ff.zero(),
            ff.zero(),
            ff.zero(),
            ff.one(),
        ];
        let roots = find_roots(&ff, &coeffs);
        let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
        vals.sort();
        assert_eq!(vals, vec![
            BigUint::from(1u32), BigUint::from(2u32),
            BigUint::from(3u32), BigUint::from(4u32),
        ]);
    }
}
