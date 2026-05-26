//! Homogenization helpers for GB computation.
//!
//! Provides the lift / homogenize / dehomogenize primitives used by
//! [`crate::gb::gb_homog::compute_gb_by_homog`].
//!
//! Background. Plain Buchberger on a non-homogeneous input in
//! `P = GF(p)[x_1, ..., x_n]` suffers from sugar mis-prediction: S-pairs
//! are processed out of true degree order, generating spurious
//! high-degree intermediates. Adding a fresh variable `h` and
//! homogenizing every input to a fixed degree makes sugar = weighted
//! degree exactly, so S-pairs are processed in strict ascending degree.
//! Dehomogenizing (`h := 1`) is linear-time, and the result is then
//! interreduced.
//!
//! The `ext` ring is a regular [`FfPolyRing`] with `n + 1` variables;
//! the extra variable `h` lives at index `n` (= `base.n_vars()`).

use crate::ff::field::PrimeField;
use crate::poly::{FfPolyRing, Poly};

/// Wraps a base polynomial ring `P` and exposes a fresh ring `Ph = P[h]`
/// with one extra "homogenizing" variable.
///
/// The extra variable `h` lives at index [`Self::h_idx`] (== `base.n_vars()`).
pub struct HomogRing<'r> {
    /// The base ring `P` (n vars).
    pub base: &'r FfPolyRing,
    /// The extended ring `Ph = P[h]` (n+1 vars; the last one is `h`).
    pub ext: FfPolyRing,
    /// Index of the homogenizing variable inside [`Self::ext`] — equals `base.n_vars()`.
    pub h_idx: usize,
}

impl<'r> HomogRing<'r> {
    /// Build a fresh extended ring `Ph` with one more variable than `base`.
    /// The extra variable is named `__h` (chosen to avoid collisions with
    /// circuit signal names which never start with `__`).
    ///
    /// `Ph` constructs a fresh `PrimeField` over the same prime as
    /// `base.field()`. Coefficient moves between `base.ring` and
    /// `ext.ring` are sound because `FieldElem` arithmetic dispatches
    /// on the `PrimeField` passed to each op — the field identity
    /// itself is irrelevant once the prime matches.
    pub fn new(base: &'r FfPolyRing) -> Self {
        let n = base.n_vars();
        let mut var_names = base.var_names().to_vec();
        var_names.push("__h".to_string());
        let ext_field = PrimeField::new(base.field().prime().clone());
        let ext = FfPolyRing::new(ext_field, var_names);
        debug_assert_eq!(ext.n_vars(), n + 1);
        HomogRing { base, ext, h_idx: n }
    }

    /// Lift a polynomial from `P` into `Ph` (φ).  This is the embedding
    /// `x_i ↦ x_i`, leaving the `h` exponent at 0 in every term.
    ///
    /// Implementation: walks `terms(p)` and rebuilds with
    /// `ext.create_monomial(iter)` where the iterator yields the same `n`
    /// exponents followed by `0`.  Coefficients are transported via
    /// `to_biguint`/`from_biguint` so the lift is independent of the
    /// `PrimeField` instance identity (the two rings carry distinct but
    /// structurally-equal `Zn` rings over the same prime — see
    /// [`Self::new`]).
    pub fn lift(&self, p: &Poly) -> Poly {
        let base_ring = &self.base.ring;
        let ext_ring = &self.ext.ring;
        let n = self.base.n_vars();
        let mut acc = ext_ring.zero();
        let mut exps_buf: Vec<usize> = vec![0; n + 1];
        for (c, m) in base_ring.terms(p) {
            let c_bi = self.base.field().to_biguint(c);
            let c_ext = self.ext.field().from_biguint(&c_bi);
            for i in 0..n {
                exps_buf[i] = base_ring.exponent_at(&m, i);
            }
            exps_buf[n] = 0;
            let mono_ext = ext_ring.create_monomial(exps_buf.iter().copied());
            let term = ext_ring.create_term(c_ext, mono_ext);
            ext_ring.add_assign(&mut acc, term);
        }
        acc
    }

    /// Homogenize a *lifted* polynomial in `Ph` (where the `h` exponent is
    /// currently 0 in every term) by raising it to its top total degree.
    ///
    /// For every term `(c, m)` with total deg `e`, replace it with
    /// `(c, m · h^{d-e})` where `d = max_e`.  Result is total-degree-`d`
    /// homogeneous in all `n+1` variables.
    pub fn homogenize(&self, q_lifted: &Poly) -> Poly {
        let ext_ring = &self.ext.ring;
        let n_plus_1 = self.ext.n_vars();
        let field = &self.ext.field();
        // Gather (coeff, exps[n+1]) and find max total deg.
        // exponent_at slot h_idx is 0 by construction of `lift`.
        let mut terms_buf: Vec<(_, Vec<usize>)> = Vec::new();
        let mut max_d: usize = 0;
        for (c, m) in ext_ring.terms(q_lifted) {
            let exps: Vec<usize> = (0..n_plus_1).map(|i| ext_ring.exponent_at(&m, i)).collect();
            let d: usize = exps.iter().sum();
            if d > max_d { max_d = d; }
            terms_buf.push((c, exps));
        }
        let mut acc = ext_ring.zero();
        for (c, mut exps) in terms_buf {
            let e: usize = exps.iter().sum();
            // bump the h slot by (max_d - e)
            exps[self.h_idx] += max_d - e;
            let mono_ext = ext_ring.create_monomial(exps.into_iter());
            let term = ext_ring.create_term(field.clone_el(c), mono_ext);
            ext_ring.add_assign(&mut acc, term);
        }
        acc
    }

    /// Convenience: lift then homogenize in one shot.
    pub fn lift_and_homogenize(&self, p: &Poly) -> Poly {
        let lifted = self.lift(p);
        self.homogenize(&lifted)
    }

    /// Dehomogenize a polynomial in `Ph` back to `P` by setting `h := 1`.
    ///
    /// Implementation: walks `terms(q)` and rebuilds with the leading `n`
    /// exponents, dropping the `h_idx` exponent.  Equivalent to
    /// `evaluate` with `value[h_idx] = 1` but cheaper (no full evaluate
    /// machinery).
    ///
    /// Note: two distinct monomials in `Ph` can collapse to the same
    /// monomial in `P` (one with `h^a · m`, another with `h^b · m`); we
    /// must therefore *accumulate* coefficients per base-monomial via
    /// `add_assign`, not just emit terms blindly.  `add_assign` on
    /// `MultivariatePolyRingImpl` already merges like-monomials.
    pub fn dehom(&self, q: &Poly) -> Poly {
        let base_ring = &self.base.ring;
        let ext_ring = &self.ext.ring;
        let n = self.base.n_vars();
        let mut acc = base_ring.zero();
        for (c, m) in ext_ring.terms(q) {
            let c_bi = self.ext.field().to_biguint(c);
            let c_base = self.base.field().from_biguint(&c_bi);
            let exps = (0..n).map(|i| ext_ring.exponent_at(&m, i));
            let mono_base = base_ring.create_monomial(exps);
            let term = base_ring.create_term(c_base, mono_base);
            base_ring.add_assign(&mut acc, term);
        }
        acc
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use num_bigint::BigUint;

    fn pr_xy() -> FfPolyRing {
        let field = PrimeField::new(BigUint::from(17u32));
        FfPolyRing::new(field, vec!["x".into(), "y".into()])
    }

    #[test]
    fn test_homog_ring_shape() {
        let pr = pr_xy();
        let h = HomogRing::new(&pr);
        assert_eq!(h.base.n_vars(), 2);
        assert_eq!(h.ext.n_vars(), 3);
        assert_eq!(h.h_idx, 2);
    }

    #[test]
    fn test_lift_preserves_zero() {
        let pr = pr_xy();
        let h = HomogRing::new(&pr);
        let z = pr.zero();
        let lifted = h.lift(&z);
        assert!(h.ext.ring.is_zero(&lifted));
    }

    #[test]
    fn test_lift_dehom_roundtrip_on_homog_input() {
        // x + y is already degree-1 homogeneous → lift, dehom should be identity.
        let pr = pr_xy();
        let h = HomogRing::new(&pr);
        let x = pr.var(0);
        let y = pr.var(1);
        let p = pr.add(x, y);
        let q = h.lift(&p);
        let p2 = h.dehom(&q);
        // Compare via subtraction zero test
        let diff = pr.sub(p, p2);
        assert!(pr.is_zero(&diff));
    }

    #[test]
    fn test_homogenize_mixed_degree() {
        // f = x^2 + y + 1 (degrees 2, 1, 0; max_d = 2)
        // homog should be: x^2 + y·h + h^2
        let pr = pr_xy();
        let h = HomogRing::new(&pr);
        let x = pr.var(0);
        let y = pr.var(1);
        let one = pr.one();
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let f = pr.add(pr.add(xx, pr.clone_poly(&y)), one);
        let lifted = h.lift(&f);
        let homog = h.homogenize(&lifted);
        // dehom(homog) should give back f exactly (h := 1).
        let back = h.dehom(&homog);
        let diff = pr.sub(pr.clone_poly(&f), back);
        assert!(pr.is_zero(&diff), "dehom(homog(lift(f))) should equal f");

        // Every term of `homog` must have total degree exactly 2.
        let ext_ring = &h.ext.ring;
        for (_, m) in ext_ring.terms(&homog) {
            let d: usize = (0..h.ext.n_vars()).map(|i| ext_ring.exponent_at(&m, i)).sum();
            assert_eq!(d, 2, "homogenized polynomial must be degree-2 homogeneous");
        }
    }

    #[test]
    fn test_homogenize_already_homog() {
        // f = x + y is degree-1 homog; lift_and_homogenize should equal lift.
        let pr = pr_xy();
        let h = HomogRing::new(&pr);
        let f = pr.add(pr.var(0), pr.var(1));
        let lifted = h.lift(&f);
        let homog = h.lift_and_homogenize(&f);
        let diff = h.ext.sub(lifted, homog);
        assert!(h.ext.is_zero(&diff));
    }
}
