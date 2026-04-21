//! Univariate root finding over GF(p) using feanor-math's Cantor-Zassenhaus.

use feanor_math::ring::*;
use feanor_math::rings::poly::dense_poly::*;
use feanor_math::rings::poly::*;
use feanor_math::algorithms::poly_factor::FactorPolyField;
use feanor_math::field::FieldStore;

use crate::field::{FfField, FfEl};

/// Find all roots of a univariate polynomial over GF(p).
///
/// `coeffs[i]` is the coefficient of x^i.
pub fn find_roots(field: &FfField, coeffs: &[FfEl]) -> Vec<FfEl> {
    let fp = field.field();
    let poly_ring = DensePolyRing::new(fp, "t");

    // Build polynomial from coefficients
    let poly = poly_ring.from_terms(
        coeffs.iter().enumerate().map(|(i, c)| (fp.clone_el(c), i))
    );

    if poly_ring.is_zero(&poly) {
        return vec![];
    }

    // Factor using Cantor-Zassenhaus
    let (factors, _unit) = <_ as FactorPolyField>::factor_poly(&poly_ring, &poly);

    // Extract roots from linear factors
    let mut roots = Vec::new();
    for (f, _mult) in factors {
        if poly_ring.degree(&f) == Some(1) {
            // f = c1*x + c0, root = -c0/c1
            let c0 = poly_ring.coefficient_at(&f, 0);
            let c1 = poly_ring.coefficient_at(&f, 1);
            let root = fp.negate(fp.div(&c0, &c1));
            roots.push(root);
        }
    }

    roots
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
}
