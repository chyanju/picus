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

// ============================================================================
// Sprint 2.5 T3 — Process-global GB strategy selector.
//
// Mirrors the `--profile`/profile.rs pattern: a single AtomicU8 holds the
// active strategy; CLI / library callers flip it before computing GBs.
// All `Ideal::new*` calls dispatch through `compute_gb_dispatch`, which
// consults this atomic and routes to either:
//   * Direct  — the existing `compute_gb_fast` (DegRevLex Buchberger on P)
//   * ByHomog — `crate::gb_homog::compute_gb_by_homog` (homogenize → GB on Ph
//                → dehom → interreduce in P)
//   * Auto    — Direct if every input is already total-degree-homogeneous,
//               otherwise ByHomog.  Cheap test (one pass over generators).
// ============================================================================

use std::sync::atomic::{AtomicU8, Ordering};

/// Strategy for computing a Groebner basis.  See [`set_gb_strategy`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GbStrategy {
    /// Plain DegRevLex Buchberger on `P` (the historical default).
    Direct = 0,
    /// CoCoA-style homogenize → GB on `P[h]` → dehomogenize → interreduce.
    /// Mirrors `myGBasisByHomog` (`SparsePolyOps-ideal.C:819-862`).
    ByHomog = 1,
    /// Pick `Direct` if every input is already homogeneous w.r.t. the
    /// total-degree grading; otherwise pick `ByHomog`.
    Auto = 2,
}

static GB_STRATEGY: AtomicU8 = AtomicU8::new(GbStrategy::Direct as u8);

/// Read the currently-active GB strategy.  Default is [`GbStrategy::Direct`].
#[inline]
pub fn gb_strategy() -> GbStrategy {
    match GB_STRATEGY.load(Ordering::Relaxed) {
        1 => GbStrategy::ByHomog,
        2 => GbStrategy::Auto,
        _ => GbStrategy::Direct,
    }
}

/// Override the process-global GB strategy.  Idempotent and thread-safe.
pub fn set_gb_strategy(s: GbStrategy) {
    GB_STRATEGY.store(s as u8, Ordering::Relaxed);
}

/// Returns true iff `p` is total-degree-homogeneous (every term has the same
/// total degree).  Empty / zero polynomials are trivially homogeneous.
fn is_total_deg_homogeneous(pr: &FfPolyRing, p: &Poly) -> bool {
    let ring = &pr.ring;
    let n = pr.n_vars;
    let mut iter = ring.terms(p);
    let Some((_, m0)) = iter.next() else { return true; };
    let d0: usize = (0..n).map(|i| ring.exponent_at(m0, i)).sum();
    for (_, m) in iter {
        let d: usize = (0..n).map(|i| ring.exponent_at(m, i)).sum();
        if d != d0 { return false; }
    }
    true
}

/// Resolve [`GbStrategy::Auto`] against an actual generator set: returns
/// `Direct` if every non-zero generator is already total-degree-homogeneous,
/// otherwise `ByHomog`.
fn resolve_auto(pr: &FfPolyRing, gens: &[Poly]) -> GbStrategy {
    let all_homog = gens.iter()
        .filter(|p| !pr.is_zero(p))
        .all(|p| is_total_deg_homogeneous(pr, p));
    if all_homog { GbStrategy::Direct } else { GbStrategy::ByHomog }
}

/// Single dispatch point used by [`Ideal::new`] and [`Ideal::new_with_cancel`].
/// Honors [`gb_strategy()`].
fn compute_gb_dispatch(pr: &FfPolyRing, gens: Vec<Poly>, cancel: &CancelToken) -> Vec<Poly> {
    if gens.is_empty() {
        return Vec::new();
    }
    let strat = match gb_strategy() {
        GbStrategy::Auto => resolve_auto(pr, &gens),
        s => s,
    };
    match strat {
        GbStrategy::Direct => compute_gb_fast(pr, gens, cancel),
        GbStrategy::ByHomog => crate::gb_homog::compute_gb_by_homog(pr, gens, cancel),
        // Auto resolved above; this arm is unreachable but keeps match exhaustive.
        GbStrategy::Auto => compute_gb_fast(pr, gens, cancel),
    }
}

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
        let basis = compute_gb_dispatch(poly_ring, generators, &CancelToken::none());
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
        let basis = compute_gb_dispatch(poly_ring, generators, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        // R6 Gap F: interreduce so the basis is canonical (reduced GB).
        // This shrinks the basis, accelerates downstream reduce/min_poly,
        // and matches what cvc5/CoCoA produce.
        //
        // Sprint 2.5: when the strategy is ByHomog (or Auto-resolved-to-ByHomog),
        // `compute_gb_by_homog` already interreduces internally.  Re-running
        // here is harmless (idempotent on a reduced basis) so we keep it
        // unconditional for simplicity.
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Sprint 2.7 — extend an existing ideal by adding new generators,
    /// using *incremental* Buchberger to avoid recomputing the GB from
    /// scratch.
    ///
    /// Precondition: `self.basis` MUST be a reduced GB in `DegRevLex`
    /// (this is the invariant maintained by `new_with_cancel`).  Calling
    /// `extend_with_cancel` on an `Ideal` constructed via `from_gb` with
    /// a non-GB `basis` is undefined behaviour (silently wrong result).
    ///
    /// Returns `Err(Cancelled)` if the token fires.
    pub fn extend_with_cancel(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        // Filter out trivial zero generators.
        let ring = &self.poly_ring.ring;
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !ring.is_zero(f))
            .collect();
        if new_polys.is_empty() {
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order(
            poly_ring, known_gb, new_polys, cancel, DegRevLex,
        );
        if cancel.is_cancelled() { return Err(Cancelled); }
        // Match `new_with_cancel` behaviour: ensure the result is a
        // reduced GB (Sprint 2.7 incremental does inter_reduce inside
        // the loop on each round, but we run it once more here for
        // canonical form, matching `new_with_cancel`).
        let basis = interreduce_basis(poly_ring, basis, cancel);
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
        self.min_poly_cancel(var_idx, &CancelToken::none())
    }

    /// Cancel-aware variant of [`Self::min_poly`].
    ///
    /// Returns `None` if the cancellation token fires, the ideal is not
    /// zero-dimensional, or the search reaches the safety cap (which
    /// should not happen for circuit-derived ideals; the cap is
    /// generous, see `MIN_POLY_DEG_CAP`).
    pub fn min_poly_cancel(&self, var_idx: usize, cancel: &CancelToken) -> Option<Vec<FfEl>> {
        let _t = crate::profile::ScopedTimer::new("ideal::min_poly");
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

        let x_poly = self.poly_ring.var(var_idx);
        let one_nf = self.reduce(&ring.one());
        let mut powers: Vec<Poly> = vec![one_nf];

        // For a true zero-dim ideal, dependence MUST be found by
        // d = dim_K(R/I) which is bounded but not cheaply computable;
        // this cap is a safety net (was 256 — too small for
        // higher-degree projected ideals, see R6 Gap A).
        const MIN_POLY_DEG_CAP: usize = 4096;
        let max_deg = MIN_POLY_DEG_CAP;

        // Augmented matrix of (normal_form, dependency vector).
        // dep[i] are the coefficients of the dependency vector
        // (one entry per power 0..=current).
        let mut nfs: Vec<Poly> = Vec::new();
        let mut deps: Vec<Vec<FfEl>> = Vec::new();
        let mut pivot_monos: Vec<crate::poly::Mono> = Vec::new();

        for d in 0..=max_deg {
            if cancel.is_cancelled() { return None; }
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
/// Interreduce a Groebner basis: replace each polynomial by its normal
/// form modulo the others, drop zeros, and monic-normalize.  Iterates
/// until no leading monomial changes.  Output is the *reduced* GB
/// (canonical: every non-leading monomial of every poly is irreducible
/// w.r.t. the rest).
///
/// This shrinks `basis.len()` (often substantially) and shortens each
/// polynomial, which speeds up every subsequent `multivariate_division`,
/// `is_zero_dim`, and `min_poly` call.  Matches what cvc5/CoCoA produce
/// after Buchberger.
pub(crate) fn interreduce_basis(
    poly_ring: &FfPolyRing,
    mut basis: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("ideal::interreduce");
    let ring = &poly_ring.ring;

    // Drop zeros up front.
    basis.retain(|p| !ring.is_zero(p));
    if basis.len() <= 1 {
        // Single polynomial: just monic-normalize.
        if let Some(p) = basis.first_mut() {
            let lc = leading_coefficient(ring, p, DegRevLex);
            let fp = poly_ring.field.field();
            if !fp.is_one(&lc) && !fp.is_zero(&lc) {
                let inv = fp.div(&fp.one(), &lc);
                let inv_poly = poly_ring.constant(inv);
                *p = ring.mul_ref(&inv_poly, p);
            }
        }
        return basis;
    }

    let mut changed = true;
    let mut passes = 0usize;
    // Hard cap to avoid pathological non-termination (shouldn't happen
    // for a valid GB, but we are defensive).
    const MAX_PASSES: usize = 32;
    while changed && passes < MAX_PASSES {
        if cancel.is_cancelled() { return basis; }
        changed = false;
        passes += 1;
        let mut i = 0;
        while i < basis.len() {
            if cancel.is_cancelled() { return basis; }
            // Capture old leading monomial to detect change.
            let old_lm = leading_monomial(ring, &basis[i], DegRevLex);
            // Move out poly_i, divide by the rest, put back.
            let p_i = std::mem::replace(&mut basis[i], ring.zero());
            let nf = multivariate_division(
                ring,
                p_i,
                basis.iter().enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, q)| q),
                DegRevLex,
            );

            if ring.is_zero(&nf) {
                // Reduced to zero: drop entry.
                basis.remove(i);
                changed = true;
                continue;
            }
            // Monic-normalize.
            let lc = leading_coefficient(ring, &nf, DegRevLex);
            let fp = poly_ring.field.field();
            let nf_monic = if fp.is_one(&lc) || fp.is_zero(&lc) {
                nf
            } else {
                let inv = fp.div(&fp.one(), &lc);
                let inv_poly = poly_ring.constant(inv);
                ring.mul_ref(&inv_poly, &nf)
            };
            let new_lm = leading_monomial(ring, &nf_monic, DegRevLex);
            let lm_changed = match (&old_lm, &new_lm) {
                (None, None) => false,
                (Some(_), None) | (None, Some(_)) => true,
                (Some(a), Some(b)) => {
                    let n_vars = ring.indeterminate_count();
                    (0..n_vars).any(|i| ring.exponent_at(a, i) != ring.exponent_at(b, i))
                }
            };
            if lm_changed {
                changed = true;
            }
            basis[i] = nf_monic;
            i += 1;
        }
    }
    basis
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
    let n_gens = generators.len();
    let n_vars = poly_ring.ring.indeterminate_count();
    // Wrap in catch_unwind to gracefully handle feanor-math panics
    // (e.g., monomial degree overflow when max_supported_deg is exceeded).
    // On panic, return the original generators unreduced rather than an empty
    // basis — an empty basis would be misinterpreted as "no constraints" (SAT).
    let gens_backup: Vec<Poly> = generators.iter()
        .map(|p| poly_ring.ring.clone_el(p))
        .collect();
    let cancel_clone = cancel.clone();
    let start = std::time::Instant::now();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        compute_gb_fast_inner(poly_ring, generators, &cancel_clone)
    }));
    let elapsed = start.elapsed();
    match result {
        Ok(ref basis) => {
            log::trace!(
                "GB call: {} gens, {} vars → {} basis elems in {:.1}ms",
                n_gens, n_vars, basis.len(), elapsed.as_secs_f64() * 1000.0
            );
        }
        Err(_) => {
            log::warn!("GB computation panicked (likely degree overflow); returning generators unreduced");
        }
    }
    match result {
        Ok(basis) => basis,
        Err(_) => gens_backup,
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
    let _t = crate::profile::ScopedTimer::new("compute_gb_with_order");
    if generators.is_empty() {
        return Vec::new();
    }
    let ring = &poly_ring.ring;
    let n_vars = ring.indeterminate_count();
    let as_local_pir = AsLocalPIR::from_field(ring.base_ring());
    let max_deg = max_supported_deg(n_vars);
    let new_poly_ring = MultivariatePolyRingImpl::new_with_mult_table(
        &as_local_pir, n_vars, max_deg, mult_table_bounds(n_vars), Global,
    );
    let from_ring = new_poly_ring.lifted_hom(ring, WrapHom::to_delegate_ring(as_local_pir.get_ring()));
    let mapped: Vec<_> = generators.into_iter().map(|f| from_ring.map(f)).collect();
    let backup: Vec<_> = mapped.iter().map(|f| new_poly_ring.clone_el(f)).collect();
    let cancel_clone = cancel.clone();
    let mut stats_obs = crate::gb_stats::GbStatsObserver::default();
    let result = buchberger_observed(
        &new_poly_ring, mapped, order,
        default_sort_fn(&new_poly_ring, order),
        move |_| cancel_clone.is_cancelled(),
        DontObserve,
        &mut stats_obs,
    );
    let basis = match result { Ok(gb) => gb, Err(_) => backup };
    let to_ring = ring.lifted_hom(&new_poly_ring, UnwrapHom::from_delegate_ring(as_local_pir.get_ring()));
    basis.into_iter().map(|f| to_ring.map(f)).collect()
}

/// Sprint 2.7 — incremental GB computation.
///
/// Computes a Gröbner basis of `<known_gb> + <new_polys>` by extending
/// an existing reduced GB rather than recomputing it from scratch.  The
/// caller MUST guarantee that `known_gb` is already a reduced GB in the
/// given `order` (this holds automatically when it comes from a prior
/// `compute_gb_with_order` call followed by `interreduce_basis`).
///
/// On cancellation, returns `known_gb ++ new_polys` (the union of inputs)
/// as a best-effort fallback, mirroring `compute_gb_with_order`'s backup
/// behaviour.
pub fn compute_gb_incremental_with_order<O: MonomialOrder + Copy + Send + Sync>(
    poly_ring: &FfPolyRing,
    known_gb: Vec<Poly>,
    new_polys: Vec<Poly>,
    cancel: &CancelToken,
    order: O,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_incremental_with_order");
    // Fast paths
    if new_polys.is_empty() {
        return known_gb;
    }
    if known_gb.is_empty() {
        return compute_gb_with_order(poly_ring, new_polys, cancel, order);
    }

    let ring = &poly_ring.ring;
    let n_vars = ring.indeterminate_count();
    let as_local_pir = AsLocalPIR::from_field(ring.base_ring());
    let max_deg = max_supported_deg(n_vars);
    let new_poly_ring = MultivariatePolyRingImpl::new_with_mult_table(
        &as_local_pir, n_vars, max_deg, mult_table_bounds(n_vars), Global,
    );
    let from_ring = new_poly_ring.lifted_hom(ring, WrapHom::to_delegate_ring(as_local_pir.get_ring()));
    let mapped_known: Vec<_> = known_gb.into_iter().map(|f| from_ring.map(f)).collect();
    let mapped_new: Vec<_> = new_polys.into_iter().map(|f| from_ring.map(f)).collect();
    // Best-effort backup for cancellation: union of inputs.
    let backup: Vec<_> = mapped_known.iter().chain(mapped_new.iter())
        .map(|f| new_poly_ring.clone_el(f)).collect();
    let cancel_clone = cancel.clone();
    let mut stats_obs = crate::gb_stats::GbStatsObserver::default();
    let result = buchberger_incremental_observed(
        &new_poly_ring, mapped_known, mapped_new, order,
        default_sort_fn(&new_poly_ring, order),
        move |_| cancel_clone.is_cancelled(),
        DontObserve,
        &mut stats_obs,
    );
    let basis = match result { Ok(gb) => gb, Err(_) => backup };
    let to_ring = ring.lifted_hom(&new_poly_ring, UnwrapHom::from_delegate_ring(as_local_pir.get_ring()));
    basis.into_iter().map(|f| to_ring.map(f)).collect()
}
pub fn compute_gb_with_order_traced<O: MonomialOrder + Copy + Send + Sync>(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: O,
    tracer: &mut crate::tracer::GbTracer,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_with_order_traced");
    if generators.is_empty() {
        return Vec::new();
    }
    let ring = &poly_ring.ring;
    let n_vars = ring.indeterminate_count();
    let as_local_pir = AsLocalPIR::from_field(ring.base_ring());
    let max_deg = max_supported_deg(n_vars);
    let new_poly_ring = MultivariatePolyRingImpl::new_with_mult_table(
        &as_local_pir, n_vars, max_deg, mult_table_bounds(n_vars), Global,
    );
    let from_ring = new_poly_ring.lifted_hom(ring, WrapHom::to_delegate_ring(as_local_pir.get_ring()));
    let mapped: Vec<_> = generators.into_iter().map(|f| from_ring.map(f)).collect();
    let backup: Vec<_> = mapped.iter().map(|f| new_poly_ring.clone_el(f)).collect();
    let cancel_clone = cancel.clone();
    let mut stats_obs = crate::gb_stats::GbStatsObserver::default();
    let mut chained = crate::gb_stats::ChainedObserver::new(tracer, &mut stats_obs);
    let result = buchberger_observed(
        &new_poly_ring, mapped, order,
        default_sort_fn(&new_poly_ring, order),
        move |_| cancel_clone.is_cancelled(),
        DontObserve,
        &mut chained,
    );
    let basis = match result { Ok(gb) => gb, Err(_) => backup };
    let to_ring = ring.lifted_hom(&new_poly_ring, UnwrapHom::from_delegate_ring(as_local_pir.get_ring()));
    basis.into_iter().map(|f| to_ring.map(f)).collect()
}

/// Multiplication table bounds: `(d1, d2)` where table covers products
/// with one factor degree ≤ d1 and the other ≤ d2.  Larger tables avoid
/// the expensive decode-add-encode fallback for monomial multiplication.
/// Bounded by memory: table size ∝ C(n+d1,d1) × C(n+d2,d2) × 8 bytes.
pub(crate) fn mult_table_bounds(n_vars: usize) -> (u16, u16) {
    if n_vars <= 5 { (6, 6) }        // ~1.7MB
    else if n_vars <= 8 { (4, 4) }   // ~2MB
    else if n_vars <= 15 { (3, 3) }  // ~5MB
    else if n_vars <= 25 { (2, 3) }  // ~5-20MB
    else { (2, 2) }                   // minimal
}
/// to avoid feanor-math panics.  QF_FF constraints are at most degree 2,
/// but Buchberger S-polynomials can increase degree during reduction.
pub(crate) fn max_supported_deg(n_vars: usize) -> u16 {
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
