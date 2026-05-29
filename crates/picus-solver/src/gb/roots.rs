//! Univariate root finding over GF(p).
//!
//! Forwards to [`crate::ff::univariate::find_roots`], which runs:
//!
//! 1. Squarefree preprocessing via `gcd(f, x^q - x mod f)` to isolate
//!    distinct linear factors.
//! 2. Cantor–Zassenhaus factorisation of the squarefree part.
//!
//! Semantics match cvc5's univariate root finding.

use crate::ff::univariate::{self, UnivariatePoly};
use crate::ff::field::{FieldElem, PrimeField};
use crate::metric;

/// Find all roots of a univariate polynomial over GF(p).
///
/// `coeffs[i]` is the coefficient of x^i.
pub fn find_roots(field: &PrimeField, coeffs: &[FieldElem]) -> Vec<FieldElem> {
    find_roots_checked(field, coeffs).0
}

/// Like [`find_roots`], returning `(roots, complete)`. See
/// [`crate::ff::univariate::find_roots_checked`] for the completeness
/// contract: when `complete == false` the returned roots are only a subset
/// of the true root set, so callers must not treat exhausting them as proof
/// of infeasibility.
#[metric("find_roots")]
pub fn find_roots_checked(field: &PrimeField, coeffs: &[FieldElem]) -> (Vec<FieldElem>, bool) {
    let fp = field;
    let owned: Vec<FieldElem> = coeffs.iter().map(|c| fp.clone_el(c)).collect();
    let poly = UnivariatePoly::from_coeffs(owned, fp);
    if poly.is_zero() {
        return (Vec::new(), true);
    }
    univariate::find_roots_checked(&poly, fp)
}

#[cfg(test)]
#[path = "roots_tests.rs"]
mod tests;
