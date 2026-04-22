//! Ideal operations over GF(p)[x_1,...,x_n].
//!
//! This module wraps a Groebner basis (in any monomial order) and provides
//! the operations needed by Split GB, BitProp, and the model construction:
//!
//! * `contains(p)`         -- ideal membership: is `p ∈ I`?
//! * `reduce(p)`           -- normal form of `p` modulo `I`
//! * `is_whole_ring()`     -- is `I = R` (i.e. `1 ∈ I`)?
//! * `is_zero_dim()`       -- is `R/I` finite-dimensional as an `R`-module?
//! * `min_poly(var)`       -- minimal polynomial of a variable in `R/I`
//!                           (only meaningful when `is_zero_dim()` is true)
//! * `normalize(p)`        -- divide `p` by its leading coefficient (LC = 1)
//!
//! The implementation mirrors cvc5's `IsElem`, `NF`, `IsZeroDim` and
//! `MinPolyQuot` calls into CoCoA, but in pure Rust on top of feanor-math.

use std::collections::HashSet;

use feanor_math::algorithms::buchberger::*;
use feanor_math::computation::DontObserve;
use feanor_math::delegate::{UnwrapHom, WrapHom};
use feanor_math::field::FieldStore;
use feanor_math::homomorphism::*;
use feanor_math::ring::*;
use feanor_math::rings::local::AsLocalPIR;
use feanor_math::rings::multivariate::*;
use feanor_math::rings::multivariate::multivariate_impl::*;
use std::alloc::Global;

use crate::field::FfEl;
use crate::poly::{FfPolyRing, Poly, PolyRingType};
use crate::timeout::{CancelToken, Cancelled};

/// A Groebner basis equipped with the data needed for ideal operations.
///
/// The basis is interpreted as the generators of an ideal `I` in
/// `GF(p)[x_1,...,x_n]`.  All operations are *pure* w.r.t. `self`.
pub struct Ideal<'r> {
    pub poly_ring: &'r FfPolyRing,
    /// A Groebner basis (in `DegRevLex` order) of the ideal.  All operations
    /// reduce in this order, which is the most efficient choice.
    pub basis: Vec<Poly>,
}

impl<'r> Ideal<'r> {
    /// Wrap an existing list of polynomials as the GB of an ideal.  The
    /// polynomials must already form a Groebner basis in `DegRevLex` order.
    pub fn from_gb(poly_ring: &'r FfPolyRing, basis: Vec<Poly>) -> Self {
        Ideal { poly_ring, basis }
    }

    /// Build an ideal by computing its DegRevLex Groebner basis from a list
    /// of generators.
    pub fn new(poly_ring: &'r FfPolyRing, generators: Vec<Poly>) -> Self {
        if generators.is_empty() {
            return Ideal { poly_ring, basis: Vec::new() };
        }
        let basis = compute_gb_fast(poly_ring, generators, &CancelToken::none());
        Ideal { poly_ring, basis }
    }

    /// Build an ideal with cooperative cancellation.
    /// Returns `Err(Cancelled)` if the token fires during GB computation.
    pub fn new_with_cancel(
        poly_ring: &'r FfPolyRing,
        generators: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        if generators.is_empty() {
            return Ok(Ideal { poly_ring, basis: Vec::new() });
        }
        let basis = compute_gb_fast(poly_ring, generators, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Reduce `p` modulo the ideal.  Returns the *normal form* of `p`.
    pub fn reduce(&self, p: &Poly) -> Poly {
        let ring = &self.poly_ring.ring;
        if self.basis.is_empty() {
            return ring.clone_el(p);
        }
        multivariate_division(
            ring,
            ring.clone_el(p),
            self.basis.iter(),
            DegRevLex,
        )
    }

    /// Ideal membership: returns `true` iff `p ∈ I`.
    pub fn contains(&self, p: &Poly) -> bool {
        let r = self.reduce(p);
        self.poly_ring.ring.is_zero(&r)
    }

    /// Returns `true` iff `I = R` (i.e. `1 ∈ I`, equivalently the basis
    /// contains a non-zero constant).
    pub fn is_whole_ring(&self) -> bool {
        let ring = &self.poly_ring.ring;
        self.basis.iter().any(|p| {
            !ring.is_zero(p) && ring.appearing_indeterminates(p).is_empty()
        })
    }

    /// Returns `true` iff `R/I` is a finite-dimensional `K`-vector space.
    ///
    /// A standard result: `dim(R/I) < ∞` iff for every variable `x_i` the
    /// Groebner basis (in any order) contains a polynomial whose leading
    /// monomial is a *pure power* `x_i^k` for some `k >= 1`.
    pub fn is_zero_dim(&self) -> bool {
        if self.is_whole_ring() {
            // I = R has R/I = {0}, which is 0-dimensional.
            return true;
        }
        let ring = &self.poly_ring.ring;
        let n_vars = self.poly_ring.n_vars;

        let mut covered: HashSet<usize> = HashSet::new();
        for p in &self.basis {
            if ring.is_zero(p) {
                continue;
            }
            // Find the leading monomial (in DegRevLex)
            if let Some(lm) = leading_monomial(ring, p, DegRevLex) {
                // Check if lm is a pure power x_i^k
                let mut nonzero_var: Option<usize> = None;
                let mut multiple = false;
                for i in 0..n_vars {
                    let e = ring.exponent_at(&lm, i);
                    if e > 0 {
                        if nonzero_var.is_some() {
                            multiple = true;
                            break;
                        }
                        nonzero_var = Some(i);
                    }
                }
                if !multiple {
                    if let Some(i) = nonzero_var {
                        covered.insert(i);
                    }
                }
            }
        }
        covered.len() == n_vars
    }

    /// Compute the minimal polynomial of variable `var_idx` in `R/I`.
    ///
    /// Requires `is_zero_dim()`.  Returns the coefficients
    /// `[c_0, c_1, ..., c_d]` of the monic minimal polynomial
    /// `m(t) = c_0 + c_1 t + ... + c_d t^d` such that `m(x_var_idx) ∈ I`
    /// and no lower-degree such polynomial exists.
    ///
    /// The algorithm:
    ///   - Compute normal forms `1, x, x^2, ...` modulo `I`.
    ///   - Each normal form is a polynomial over `K` that lies in
    ///     a finite-dimensional `K`-vector space (since `R/I` is f.d.).
    ///   - Find the smallest `d` such that `1, x, ..., x^d` are
    ///     linearly dependent over `K` -- the dependency yields the
    ///     minimal polynomial.
    ///
    /// We use a simple Gaussian-elimination scheme on the coefficients
    /// of the normal forms (treated as vectors indexed by monomials).
    pub fn min_poly(&self, var_idx: usize) -> Option<Vec<FfEl>> {
        let ring = &self.poly_ring.ring;
        let fp = self.poly_ring.field.field();

        if self.is_whole_ring() {
            // R/I = 0; the minimal polynomial of any element is 1
            // (the constant 1, of degree 0).  But this is degenerate.
            return Some(vec![fp.one()]);
        }
        if !self.is_zero_dim() {
            return None;
        }

        // Compute normal forms of x^0, x^1, x^2, ... modulo I
        // and look for a linear dependency among them.
        //
        // We collect the "vectors" (monomial -> coefficient) of each
        // normal form into a row-echelon matrix and detect when a new
        // power of x can be expressed as a linear combination of
        // previous ones.

        let x_poly = self.poly_ring.var(var_idx);
        let one_nf = self.reduce(&ring.one());
        let mut powers: Vec<Poly> = vec![one_nf];

        // Limit: dimension of R/I is finite, but we don't know it.
        // A safe upper bound is the number of standard monomials, which
        // for a zero-dim ideal is a finite number.  We use a generous
        // limit that should suffice for circuits we encounter.
        let max_deg = 256usize;

        // Augmented matrix of (normal_form, dependency vector).
        // dep[i] are the coefficients of the dependency vector
        // (one entry per power 0..=current).
        let mut nfs: Vec<Poly> = Vec::new();
        let mut deps: Vec<Vec<FfEl>> = Vec::new();
        let mut pivot_monos: Vec<crate::poly::Mono> = Vec::new();

        for d in 0..=max_deg {
            let nf = if d == 0 {
                ring.clone_el(&powers[0])
            } else {
                let prev = ring.clone_el(&powers[d - 1]);
                let next = ring.mul_ref(&prev, &x_poly);
                self.reduce(&next)
            };
            if d > 0 {
                powers.push(ring.clone_el(&nf));
            }

            // Build row vector to reduce: (nf, e_d) where e_d is the
            // standard basis vector with a 1 in position d.
            let mut row_poly = ring.clone_el(&nf);
            let mut row_dep: Vec<FfEl> = vec![fp.zero(); d + 1];
            row_dep[d] = fp.one();

            // Reduce row against existing rows in echelon form
            for (i, nf_i) in nfs.iter().enumerate() {
                let lm_i = &pivot_monos[i];
                let coeff_at_lm = poly_coefficient_at_monomial(ring, &row_poly, lm_i);
                if !fp.is_zero(&coeff_at_lm) {
                    // Subtract (coeff_at_lm / lc_i) * row_i from row
                    let lc_i = poly_coefficient_at_monomial(ring, nf_i, lm_i);
                    debug_assert!(!fp.is_zero(&lc_i));
                    let factor = fp.div(&coeff_at_lm, &lc_i);
                    let factor_poly = self.poly_ring.constant(fp.clone_el(&factor));

                    let scaled_nf = ring.mul_ref(&factor_poly, nf_i);
                    row_poly = ring.sub(row_poly, scaled_nf);

                    // Pad deps[i] to length d+1 with zeros, subtract factor*deps[i]
                    let dep_i = &deps[i];
                    for k in 0..dep_i.len() {
                        let prod = fp.mul_ref(&factor, &dep_i[k]);
                        fp.sub_assign(&mut row_dep[k], prod);
                    }
                }
            }

            if ring.is_zero(&row_poly) {
                // Dependency found! row_dep gives the coefficients of
                // the minimal polynomial (lowest-degree dependency).
                // Make it monic: divide by leading (highest-degree non-zero) entry.
                let mut top = row_dep.len();
                while top > 0 && fp.is_zero(&row_dep[top - 1]) {
                    top -= 1;
                }
                if top == 0 {
                    // Zero polynomial -- shouldn't happen, means I = R.
                    return Some(vec![fp.one()]);
                }
                let lead = fp.clone_el(&row_dep[top - 1]);
                let mut coeffs = Vec::with_capacity(top);
                for k in 0..top {
                    coeffs.push(fp.div(&row_dep[k], &lead));
                }
                return Some(coeffs);
            }

            // Add row to echelon: pick pivot = leading monomial of row_poly.
            if let Some(lm) = leading_monomial(ring, &row_poly, DegRevLex) {
                pivot_monos.push(lm);
                nfs.push(row_poly);
                deps.push(row_dep);
            }
        }

        None
    }

    /// Divide `p` by its leading coefficient (in DegRevLex).  After
    /// normalization the leading coefficient equals `1`.  Returns the
    /// normalized polynomial; if `p == 0` returns `0`.
    pub fn normalize(&self, p: &Poly) -> Poly {
        let ring = &self.poly_ring.ring;
        let fp = self.poly_ring.field.field();

        if ring.is_zero(p) {
            return ring.zero();
        }
        let lc = leading_coefficient(ring, p, DegRevLex);
        if fp.is_zero(&lc) || fp.is_one(&lc) {
            return ring.clone_el(p);
        }
        let inv = fp.div(&fp.one(), &lc);
        let inv_poly = self.poly_ring.constant(inv);
        ring.mul_ref(&inv_poly, p)
    }
}

/// Get the leading monomial of a polynomial in a given monomial order.
pub fn leading_monomial<O: MonomialOrder + Copy>(
    ring: &PolyRingType,
    p: &Poly,
    order: O,
) -> Option<crate::poly::Mono> {
    let mut best: Option<crate::poly::Mono> = None;
    for (_, m) in ring.terms(p) {
        match &best {
            None => best = Some(ring.clone_monomial(m)),
            Some(cur) => {
                if order.compare(ring, m, cur) == std::cmp::Ordering::Greater {
                    best = Some(ring.clone_monomial(m));
                }
            }
        }
    }
    best
}

/// Get the leading coefficient of a polynomial in a given monomial order.
pub fn leading_coefficient<O: MonomialOrder + Copy>(
    ring: &PolyRingType,
    p: &Poly,
    order: O,
) -> FfEl {
    let fp = ring.base_ring();
    let mut best: Option<(crate::poly::Mono, FfEl)> = None;
    for (c, m) in ring.terms(p) {
        match &best {
            None => best = Some((ring.clone_monomial(m), fp.clone_el(c))),
            Some((cur_m, _)) => {
                if order.compare(ring, m, cur_m) == std::cmp::Ordering::Greater {
                    best = Some((ring.clone_monomial(m), fp.clone_el(c)));
                }
            }
        }
    }
    best.map(|(_, c)| c).unwrap_or_else(|| fp.zero())
}

/// Compute a DegRevLex Groebner basis of `generators` using a custom inner
/// ring with a *small* multiplication table.  This avoids the 3+ seconds
/// per-call cost of `buchberger_simple`, which internally constructs
/// `MultivariatePolyRingImpl::new(...)` (default mult-table `(6,8)`,
/// O(C(n+8,8)^2) precomputation) on every invocation.
///
/// We mirror `buchberger_simple` exactly except for the inner-ring
/// configuration: `max_supported_deg=16`, `max_multiplication_table=(2,2)`.
/// This is sufficient for QF_FF circuits (constraints are typically linear or
/// Rabinowitsch quadratic; field polys `x^p - x` are accommodated by
/// `max_supported_deg`).
fn compute_gb_fast(poly_ring: &FfPolyRing, generators: Vec<Poly>, cancel: &CancelToken) -> Vec<Poly> {
    // Wrap in catch_unwind to gracefully handle feanor-math panics
    // (e.g., monomial degree overflow when max_supported_deg is exceeded).
    // On panic, return the original generators unreduced rather than an empty
    // basis — an empty basis would be misinterpreted as "no constraints" (SAT).
    let gens_backup: Vec<Poly> = generators.iter()
        .map(|p| poly_ring.ring.clone_el(p))
        .collect();
    let cancel_clone = cancel.clone();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compute_gb_fast_inner(poly_ring, generators, &cancel_clone)
    }));
    match result {
        Ok(basis) => basis,
        Err(_) => {
            log::warn!("GB computation panicked (likely degree overflow); returning generators unreduced");
            gens_backup
        }
    }
}

fn compute_gb_fast_inner(poly_ring: &FfPolyRing, generators: Vec<Poly>, cancel: &CancelToken) -> Vec<Poly> {
    compute_gb_with_order(poly_ring, generators, cancel, DegRevLex)
}

/// Compute a GB in a specified monomial order using the optimized `(2,2)`
/// multiplication table.  This is the shared implementation for both
/// DegRevLex (used by `Ideal::new`) and Lex (used by the single-GB solver).
pub fn compute_gb_with_order<O: MonomialOrder + Copy + Send + Sync>(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: O,
) -> Vec<Poly> {
    if generators.is_empty() {
        return Vec::new();
    }
    let ring = &poly_ring.ring;
    let n_vars = ring.indeterminate_count();
    let as_local_pir = AsLocalPIR::from_field(ring.base_ring());
    let max_deg = max_supported_deg(n_vars);
    let new_poly_ring = MultivariatePolyRingImpl::new_with_mult_table(
        &as_local_pir, n_vars, max_deg, (2, 2), Global,
    );
    let from_ring = new_poly_ring.lifted_hom(ring, WrapHom::to_delegate_ring(as_local_pir.get_ring()));
    let mapped: Vec<_> = generators.into_iter().map(|f| from_ring.map(f)).collect();
    let backup: Vec<_> = mapped.iter().map(|f| new_poly_ring.clone_el(f)).collect();
    let cancel_clone = cancel.clone();
    let result = buchberger(
        &new_poly_ring, mapped, order,
        default_sort_fn(&new_poly_ring, order),
        move |_| cancel_clone.is_cancelled(),
        DontObserve,
    );
    let basis = match result { Ok(gb) => gb, Err(_) => backup };
    let to_ring = ring.lifted_hom(&new_poly_ring, UnwrapHom::from_delegate_ring(as_local_pir.get_ring()));
    basis.into_iter().map(|f| to_ring.map(f)).collect()
}

/// Like [`compute_gb_with_order`], but accepts a [`GbTracer`] for
/// UNSAT core tracing.  The observer receives callbacks as the Buchberger
/// algorithm derives new polynomials.
pub fn compute_gb_with_order_traced<O: MonomialOrder + Copy + Send + Sync>(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: O,
    tracer: &mut crate::tracer::GbTracer,
) -> Vec<Poly> {
    if generators.is_empty() {
        return Vec::new();
    }
    let ring = &poly_ring.ring;
    let n_vars = ring.indeterminate_count();
    let as_local_pir = AsLocalPIR::from_field(ring.base_ring());
    let max_deg = max_supported_deg(n_vars);
    let new_poly_ring = MultivariatePolyRingImpl::new_with_mult_table(
        &as_local_pir, n_vars, max_deg, (2, 2), Global,
    );
    let from_ring = new_poly_ring.lifted_hom(ring, WrapHom::to_delegate_ring(as_local_pir.get_ring()));
    let mapped: Vec<_> = generators.into_iter().map(|f| from_ring.map(f)).collect();
    let backup: Vec<_> = mapped.iter().map(|f| new_poly_ring.clone_el(f)).collect();
    let cancel_clone = cancel.clone();
    let result = buchberger_observed(
        &new_poly_ring, mapped, order,
        default_sort_fn(&new_poly_ring, order),
        move |_| cancel_clone.is_cancelled(),
        DontObserve,
        tracer,
    );
    let basis = match result { Ok(gb) => gb, Err(_) => backup };
    let to_ring = ring.lifted_hom(&new_poly_ring, UnwrapHom::from_delegate_ring(as_local_pir.get_ring()));
    basis.into_iter().map(|f| to_ring.map(f)).collect()
}

/// Maximum supported polynomial degree for the inner ring, based on
/// variable count.  Must satisfy C(n_vars + max_deg, n_vars) < 2^63
/// to avoid feanor-math panics.  QF_FF constraints are at most degree 2,
/// but Buchberger S-polynomials can increase degree during reduction.
fn max_supported_deg(n_vars: usize) -> u16 {
    if n_vars <= 4 { 256 }
    else if n_vars <= 8 { 64 }
    else if n_vars <= 20 { 32 }
    else if n_vars <= 50 { 16 }
    else if n_vars <= 200 { 8 }
    else { 4 }
}

/// Get the coefficient of a specific monomial in `p`.
fn poly_coefficient_at_monomial(
    ring: &PolyRingType,
    p: &Poly,
    target: &crate::poly::Mono,
) -> FfEl {
    let fp = ring.base_ring();
    let mut acc = fp.zero();
    let n_vars = ring.indeterminate_count();
    for (c, m) in ring.terms(p) {
        let mut equal = true;
        for i in 0..n_vars {
            if ring.exponent_at(m, i) != ring.exponent_at(target, i) {
                equal = false;
                break;
            }
        }
        if equal {
            fp.add_assign(&mut acc, fp.clone_el(c));
        }
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::FfField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> FfField {
        FfField::new(&BigUint::from(p))
    }

    #[test]
    fn test_contains_simple() {
        // I = (x - 3) over GF(17).  Then (x^2 - 9) ∈ I, but x ∉ I.
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let three = pr.field.from_int(3);
        let nine = pr.field.from_int(9);
        let p1 = pr.sub(pr.var(0), pr.constant(three));
        let ideal = Ideal::new(&pr, vec![p1]);

        let x = pr.var(0);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let x2_minus_9 = pr.sub(x2, pr.constant(nine));
        assert!(ideal.contains(&x2_minus_9));
        assert!(!ideal.contains(&x));
    }

    #[test]
    fn test_whole_ring() {
        // I = (1) is whole ring
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let one = pr.one();
        let ideal = Ideal::new(&pr, vec![one]);
        assert!(ideal.is_whole_ring());
        assert!(ideal.is_zero_dim());
    }

    #[test]
    fn test_is_zero_dim_yes() {
        // I = (x - 1, y - 2) over GF(17): zero-dim, single point.
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
        let one = pr.field.from_int(1);
        let two = pr.field.from_int(2);
        let p1 = pr.sub(pr.var(0), pr.constant(one));
        let p2 = pr.sub(pr.var(1), pr.constant(two));
        let ideal = Ideal::new(&pr, vec![p1, p2]);
        assert!(ideal.is_zero_dim());
    }

    #[test]
    fn test_is_zero_dim_no() {
        // I = (x*y) over GF(17): not zero-dim (positive dim variety).
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let ideal = Ideal::new(&pr, vec![xy]);
        assert!(!ideal.is_zero_dim());
    }

    #[test]
    fn test_min_poly_constant_var() {
        // I = (x - 5) over GF(17).  Min poly of x is t - 5.
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let five = pr.field.from_int(5);
        let p1 = pr.sub(pr.var(0), pr.constant(five));
        let ideal = Ideal::new(&pr, vec![p1]);
        let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
        // Should be [c0, 1] with c0 = -5 = 12 mod 17
        assert_eq!(mp.len(), 2);
        let fp = pr.field.field();
        let neg_five = fp.negate(pr.field.from_int(5));
        assert!(fp.eq_el(&mp[0], &neg_five));
        assert!(fp.is_one(&mp[1]));
    }

    #[test]
    fn test_min_poly_quadratic() {
        // I = (x^2 - 1) over GF(17).  Min poly of x is t^2 - 1.
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let x = pr.var(0);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let one = pr.one();
        let p = pr.sub(x2, one);
        let ideal = Ideal::new(&pr, vec![p]);
        let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
        assert_eq!(mp.len(), 3);
        let fp = pr.field.field();
        let neg_one = fp.negate(fp.one());
        assert!(fp.eq_el(&mp[0], &neg_one));
        assert!(fp.is_zero(&mp[1]));
        assert!(fp.is_one(&mp[2]));
    }

    #[test]
    fn test_normalize() {
        // p = 3x + 6 over GF(17), LC = 3, inverse = 6 (3*6=18=1).
        // Normalized: 6 * (3x + 6) = 18x + 36 = x + 2.
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let three = pr.field.from_int(3);
        let six = pr.field.from_int(6);
        let term1 = pr.scale(three, pr.var(0));
        let p = pr.add(term1, pr.constant(six));
        let ideal = Ideal::new(&pr, vec![]);
        let normalized = ideal.normalize(&p);
        // Check LC = 1
        let lc = leading_coefficient(&pr.ring, &normalized, DegRevLex);
        assert!(pr.field.field().is_one(&lc));
    }
}
