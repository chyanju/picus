//! Univariate root finding over GF(p).
//!
//! Forwards to [`crate::ff::univariate::find_roots`], which runs:
//!
//! 1. Squarefree preprocessing via `gcd(f, x^q - x mod f)` to isolate
//!    distinct linear factors.
//! 2. Cantor–Zassenhaus factorisation of the squarefree part.
//!
//! Semantics match cvc5's `theory/ff/uni_roots.cpp`.

use crate::ff::univariate::{self, UnivariatePoly};
use crate::field::{FfEl, FfField};

/// Find all roots of a univariate polynomial over GF(p).
///
/// `coeffs[i]` is the coefficient of x^i.
pub fn find_roots(field: &FfField, coeffs: &[FfEl]) -> Vec<FfEl> {
    let _t = crate::profile::ScopedTimer::new("find_roots");
    let fp = field;
    let owned: Vec<FfEl> = coeffs.iter().map(|c| fp.clone_el(c)).collect();
    let poly = UnivariatePoly::from_coeffs(owned, fp);
    if poly.is_zero() {
        return Vec::new();
    }
    univariate::find_roots(&poly, fp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_roots_linear() {
        // x - 3 = 0 over GF(17) → root = 3
        let ff = FfField::new(BigUint::from(17u32));

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
        let ff = FfField::new(BigUint::from(17u32));

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
        let ff = FfField::new(BigUint::from(3u32));

        let coeffs = vec![ff.one(), ff.zero(), ff.one()];
        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 0);
    }

    #[test]
    fn test_roots_with_zero_root() {
        // x^2 - x = 0 over GF(7) → roots 0, 1
        let ff = FfField::new(BigUint::from(7u32));
        let coeffs = vec![ff.zero(), ff.from_biguint(&BigUint::from(6u32)), ff.one()];
        let roots = find_roots(&ff, &coeffs);
        assert_eq!(roots.len(), 2);
        let mut vals: Vec<BigUint> = roots.iter().map(|r| ff.to_biguint(r)).collect();
        vals.sort();
        assert_eq!(vals, vec![BigUint::from(0u32), BigUint::from(1u32)]);
    }

    #[test]
    fn test_roots_high_degree_with_irreducible_factors() {
        // x^4 - 1 over GF(5): a^4 ≡ 1 mod 5 for all a ∈ {1,2,3,4}.
        let ff = FfField::new(BigUint::from(5u32));
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
