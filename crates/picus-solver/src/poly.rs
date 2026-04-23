//! Multivariate polynomial ring over GF(p) using feanor-math.

use feanor_math::ring::*;
use feanor_math::rings::multivariate::*;
use feanor_math::rings::multivariate::multivariate_impl::*;
use feanor_math::homomorphism::*;
use std::alloc::Global;

use crate::field::{FfField, FfFieldType, FfEl};
use crate::ideal::{max_supported_deg, mult_table_bounds};

/// Type alias for our polynomial ring.
pub type PolyRingType = MultivariatePolyRingImpl<FfFieldType>;
/// Type alias for a polynomial element.
pub type Poly = El<PolyRingType>;
/// Type alias for a monomial.
pub type Mono = <MultivariatePolyRingImplBase<FfFieldType> as MultivariatePolyRing>::Monomial;

/// A multivariate polynomial ring over GF(p) with named variables.
pub struct FfPolyRing {
    pub field: FfField,
    pub ring: PolyRingType,
    pub n_vars: usize,
    pub var_names: Vec<String>,
}

impl FfPolyRing {
    /// Create a new polynomial ring GF(p)[x0, x1, ..., x_{n-1}].
    pub fn new(field: FfField, var_names: Vec<String>) -> Self {
        let n_vars = var_names.len();
        // Choose a small multiplication-table size to avoid the O(C(n+d,d)^2)
        // precomputation cost.  feanor-math's default of (6,8) is wildly
        // expensive for n_vars >= ~10 (3+ seconds at startup).  Most ZK
        // circuits we encode have polynomials of total degree <= 2 (linear
        // constraints + Rabinowitsch quadratic + bitsum), so a table covering
        // (2, 2) suffices for hot multiplications.  See `ideal::max_supported_deg`
        // and `ideal::mult_table_bounds` for the shared sizing tables.
        let max_supported_deg = max_supported_deg(n_vars);
        let table = mult_table_bounds(n_vars);
        let ring = MultivariatePolyRingImpl::new_with_mult_table(
            field.field().clone(),
            n_vars,
            max_supported_deg,
            table,
            Global,
        );
        FfPolyRing { field, ring, n_vars, var_names }
    }

    /// Get the i-th indeterminate as a polynomial.
    pub fn var(&self, index: usize) -> Poly {
        let mono = self.ring.indeterminate(index);
        self.ring.create_term(self.field.one(), mono)
    }

    /// Constant polynomial from a field element.
    pub fn constant(&self, el: FfEl) -> Poly {
        self.ring.inclusion().map(el)
    }

    pub fn zero(&self) -> Poly { self.ring.zero() }
    pub fn one(&self) -> Poly { self.ring.one() }

    pub fn add(&self, a: Poly, b: Poly) -> Poly { self.ring.add(a, b) }
    pub fn sub(&self, a: Poly, b: Poly) -> Poly { self.ring.sub(a, b) }
    pub fn mul(&self, a: Poly, b: Poly) -> Poly { self.ring.mul(a, b) }
    pub fn neg(&self, a: Poly) -> Poly { self.ring.negate(a) }
    pub fn clone_poly(&self, p: &Poly) -> Poly { self.ring.clone_el(p) }
    pub fn is_zero(&self, p: &Poly) -> bool { self.ring.is_zero(p) }

    /// Get a raw reference to the ring (for advanced operations like pow).
    pub fn ring(&self) -> &PolyRingType { &self.ring }

    /// Multiply polynomial by a scalar.
    pub fn scale(&self, coeff: FfEl, poly: Poly) -> Poly {
        let c = self.constant(coeff);
        self.ring.mul(c, poly)
    }

    /// Look up variable index by name.
    pub fn var_index(&self, name: &str) -> Option<usize> {
        self.var_names.iter().position(|n| n == name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_poly_basic() {
        let field = FfField::new(&BigUint::from(17u32));
        let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);

        let x = pr.var(0);
        let y = pr.var(1);
        let sum = pr.add(x, y);
        assert!(!pr.is_zero(&sum));

        let neg_sum = pr.neg(pr.clone_poly(&sum));
        let zero = pr.add(sum, neg_sum);
        assert!(pr.is_zero(&zero));
    }
}
