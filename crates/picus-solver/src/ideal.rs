//! Ideal operations over GF(p)[x_1,...,x_n].
//!
//! Thin shim over the inlined `crate::ff` Buchberger / Ideal implementation.
//! The historical feanor-math backend has been removed; the public API
//! (`Ideal`, `compute_gb_with_order{,_traced}`, `interreduce_basis`,
//! `leading_monomial`, `leading_coefficient`, `GbStrategy`) is preserved
//! for the rest of the crate (and for `picus-cli` / `picus-smt`).

use std::collections::HashSet;

use crate::ff::buchberger::{
    self, BuchbergerConfig, GBasis, Ideal as FfIdeal, IncrementalGB,
};
use crate::ff::monomial::MonomialOrder as FfOrder;
use crate::field::FfEl;
use crate::poly::{FfPolyRing, Mono, Poly, PolyRingType};
use crate::timeout::{CancelToken, Cancelled};

// ───────────────────── Process-global GB strategy ─────────────────────────

use std::sync::atomic::{AtomicU8, Ordering};

/// Strategy for computing a Groebner basis. See [`set_gb_strategy`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GbStrategy {
    /// Plain DegRevLex Buchberger on `P` (the historical default).
    Direct = 0,
    /// CoCoA-style homogenize → GB on `P[h]` → dehomogenize → interreduce.
    ByHomog = 1,
    /// Pick `Direct` if every input is already homogeneous w.r.t. the
    /// total-degree grading; otherwise pick `ByHomog`.
    Auto = 2,
}

static GB_STRATEGY: AtomicU8 = AtomicU8::new(GbStrategy::Direct as u8);

#[inline]
pub fn gb_strategy() -> GbStrategy {
    match GB_STRATEGY.load(Ordering::Relaxed) {
        1 => GbStrategy::ByHomog,
        2 => GbStrategy::Auto,
        _ => GbStrategy::Direct,
    }
}

pub fn set_gb_strategy(s: GbStrategy) {
    GB_STRATEGY.store(s as u8, Ordering::Relaxed);
}

fn is_total_deg_homogeneous(pr: &FfPolyRing, p: &Poly) -> bool {
    let ring = &pr.ring;
    let n = pr.n_vars;
    let mut iter = ring.terms(p);
    let Some((_, m0)) = iter.next() else { return true; };
    let d0: usize = (0..n).map(|i| ring.exponent_at(&m0, i)).sum();
    for (_, m) in iter {
        let d: usize = (0..n).map(|i| ring.exponent_at(&m, i)).sum();
        if d != d0 { return false; }
    }
    true
}

fn resolve_auto(pr: &FfPolyRing, gens: &[Poly]) -> GbStrategy {
    let all_homog = gens.iter()
        .filter(|p| !pr.is_zero(p))
        .all(|p| is_total_deg_homogeneous(pr, p));
    if all_homog { GbStrategy::Direct } else { GbStrategy::ByHomog }
}

fn compute_gb_dispatch(pr: &FfPolyRing, gens: Vec<Poly>, cancel: &CancelToken) -> Vec<Poly> {
    if gens.is_empty() {
        return Vec::new();
    }
    let strat = match gb_strategy() {
        GbStrategy::Auto => resolve_auto(pr, &gens),
        s => s,
    };
    match strat {
        GbStrategy::Direct => compute_gb_with_order(pr, gens, cancel, FfOrder::DegRevLex),
        GbStrategy::ByHomog => crate::gb_homog::compute_gb_by_homog(pr, gens, cancel),
        GbStrategy::Auto => unreachable!("Auto resolved above"),
    }
}

// ─────────────────────────────── Ideal ─────────────────────────────────────

/// A Groebner basis equipped with the data needed for ideal operations.
pub struct Ideal<'r> {
    pub poly_ring: &'r FfPolyRing,
    /// A Groebner basis (in `DegRevLex` order) of the ideal.
    pub basis: Vec<Poly>,
}

impl<'r> Ideal<'r> {
    /// Wrap an existing list of polynomials as the GB of an ideal.
    pub fn from_gb(poly_ring: &'r FfPolyRing, basis: Vec<Poly>) -> Self {
        Ideal { poly_ring, basis }
    }

    /// Build an ideal by computing its DegRevLex Groebner basis.
    pub fn new(poly_ring: &'r FfPolyRing, generators: Vec<Poly>) -> Self {
        if generators.is_empty() {
            return Ideal { poly_ring, basis: Vec::new() };
        }
        let basis = compute_gb_dispatch(poly_ring, generators, &CancelToken::none());
        Ideal { poly_ring, basis }
    }

    /// Build an ideal with cooperative cancellation.
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
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Extend an existing ideal by adding new generators incrementally.
    pub(crate) fn extend_with_cancel(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !f.is_zero())
            .collect();
        if new_polys.is_empty() {
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order(
            poly_ring, known_gb, new_polys, cancel, FfOrder::DegRevLex,
        );
        if cancel.is_cancelled() { return Err(Cancelled); }
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Traced variant of `extend_with_cancel`.
    ///
    /// Feeds Buchberger observer events to the supplied `tracer`, which
    /// must be sized for at least `self.basis.len() + new_polys.len()` (after
    /// the zero filter).  When the resulting ideal is the whole ring, callers
    /// can extract a precise UNSAT core via `tracer.unsat_core_for_trivial`.
    ///
    /// The tracer's input numbering matches the order generators are added:
    /// first all elements of `self.basis` (already a reduced GB), then all
    /// surviving `new_polys`.
    #[allow(dead_code)] // future Task 07 #3 retry — see plan
    pub(crate) fn extend_with_cancel_traced(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
        tracer: &mut crate::tracer::GbTracer,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !f.is_zero())
            .collect();
        if new_polys.is_empty() {
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order_traced(
            poly_ring, known_gb, new_polys, cancel, FfOrder::DegRevLex, tracer,
        );
        if cancel.is_cancelled() { return Err(Cancelled); }
        // NOTE: do NOT inter-reduce here — the trivial-element parents in
        // `tracer` are precise only when Buchberger aborted on trivial.
        // Inter-reduce would mutate basis indices and require additional
        // dep tracking; for the linear-fast-path UNSAT detection we only
        // need to know is_whole_ring, which is preserved.
        Ok(Ideal { poly_ring, basis })
    }

    /// Reduce `p` modulo the ideal. Returns the *normal form* of `p`.
    pub fn reduce(&self, p: &Poly) -> Poly {
        if self.basis.is_empty() {
            return p.clone();
        }
        let ring = &self.poly_ring.ctx();
        p.reduce_by(&self.basis, ring)
    }

    /// Ideal membership: returns `true` iff `p ∈ I`.
    pub fn contains(&self, p: &Poly) -> bool {
        self.reduce(p).is_zero()
    }

    /// Returns `true` iff `I = R` (i.e. `1 ∈ I`).
    pub fn is_whole_ring(&self) -> bool {
        self.basis.iter().any(|p| !p.is_zero() && p.is_constant())
    }

    /// Returns `true` iff `R/I` is a finite-dimensional `K`-vector space.
    pub fn is_zero_dim(&self) -> bool {
        if self.is_whole_ring() {
            return true;
        }
        if self.basis.is_empty() {
            return false;
        }
        let ring = self.poly_ring.ctx();
        let n_vars = self.poly_ring.n_vars;

        let mut covered: HashSet<usize> = HashSet::new();
        for p in &self.basis {
            if p.is_zero() { continue; }
            if let Some(lm) = p.leading_monomial(ring) {
                let exps = lm.exponents();
                let mut nonzero_var: Option<usize> = None;
                let mut multiple = false;
                for i in 0..n_vars {
                    if exps[i] > 0 {
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

    /// Compute the minimal polynomial of `var_idx` in `R/I`.
    pub fn min_poly(&self, var_idx: usize) -> Option<Vec<FfEl>> {
        self.min_poly_cancel(var_idx, &CancelToken::none())
    }

    /// Cancel-aware variant of [`Self::min_poly`].
    pub fn min_poly_cancel(&self, var_idx: usize, cancel: &CancelToken) -> Option<Vec<FfEl>> {
        let _t = crate::profile::ScopedTimer::new("ideal::min_poly");
        let ring = self.poly_ring.ctx().clone();
        let ff_ideal = FfIdeal::new(ring, self.basis.iter().map(|p| p.clone()).collect());
        ff_ideal.min_poly_cancel(var_idx, cancel)
    }

    /// Divide `p` by its leading coefficient (in DegRevLex). LC becomes 1.
    pub fn normalize(&self, p: &Poly) -> Poly {
        if p.is_zero() { return Poly::zero(); }
        let ring = self.poly_ring.ctx();
        p.make_monic(ring)
    }
}

// ────────────────────── Standalone ring helpers ───────────────────────────

/// Get the leading monomial of a polynomial in a given monomial order.
///
/// The order parameter is accepted for API compatibility; the polynomial's
/// own ring already stores terms in canonical descending order
/// (`PolyRing.order`), so we just return the first term's monomial.
pub fn leading_monomial(
    ring: &PolyRingType,
    p: &Poly,
    _order: FfOrder,
) -> Option<Mono> {
    p.leading_monomial(&ring.ctx)
}

/// Get the leading coefficient of a polynomial in a given monomial order.
pub fn leading_coefficient(
    ring: &PolyRingType,
    p: &Poly,
    _order: FfOrder,
) -> FfEl {
    match p.leading_coefficient() {
        Some(c) => ring.base_ring().clone_el(c),
        None => ring.base_ring().zero(),
    }
}

// ─────────────────────── interreduce_basis ────────────────────────────────

/// Interreduce a Groebner basis: replace each polynomial by its normal form
/// modulo the others, drop zeros, and monic-normalize. Output is the
/// *reduced* GB.
pub(crate) fn interreduce_basis(
    poly_ring: &FfPolyRing,
    basis: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("ideal::interreduce");
    if cancel.is_cancelled() {
        return basis;
    }
    buchberger::interreduce(basis, poly_ring.ctx())
}

// ──────────────────── compute_gb_with_order family ────────────────────────

/// Build a per-call `ff::PolyRing` whose monomial order matches `order`.
/// Cheap (an `Arc<PolyRing>` with the same field/var-name data).
pub(crate) fn ring_for_order(poly_ring: &FfPolyRing, order: FfOrder) -> std::sync::Arc<crate::ff::polynomial::PolyRing> {
    crate::ff::polynomial::PolyRing::new(
        poly_ring.field.field().clone(),
        poly_ring.var_names.clone(),
        order,
    )
}

/// Compute a Groebner basis of `generators` in the requested monomial order.
pub fn compute_gb_with_order(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_with_order");
    if generators.is_empty() {
        return Vec::new();
    }
    let n_gens = generators.len();
    let n_vars = poly_ring.n_vars;
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
    };
    let start = std::time::Instant::now();
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        buchberger::groebner_basis(generators, &ring, &cfg)
    }));
    let elapsed = start.elapsed();
    let basis = match result {
        Ok(Ok(GBasis { basis, .. })) => basis,
        Ok(Err(_)) => backup,
        Err(_) => {
            log::warn!("GB computation panicked; returning generators unreduced");
            backup
        }
    };
    log::trace!(
        "GB call: {} gens, {} vars → {} basis elems in {:.1}ms",
        n_gens, n_vars, basis.len(), elapsed.as_secs_f64() * 1000.0
    );
    basis
}

/// Incremental GB extension. Computes GB of `<known_gb> + <new_polys>`,
/// reusing `known_gb` as a *trusted reduced GB seed*: no S-pairs among
/// `known_gb` elements need to be processed (Buchberger criterion), so the
/// seeding pass only generates and discharges S-pairs *between* `known_gb`
/// and `new_polys`, plus among `new_polys` themselves. This is the genuine
/// incremental Buchberger path that the legacy concat-and-rerun version
/// emulated only superficially.
pub fn compute_gb_incremental_with_order(
    poly_ring: &FfPolyRing,
    known_gb: Vec<Poly>,
    new_polys: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_incremental_with_order");
    if new_polys.is_empty() {
        return known_gb;
    }
    if known_gb.is_empty() {
        return compute_gb_with_order(poly_ring, new_polys, cancel, order);
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
    };

    // Backup for panic / error fallback (matches compute_gb_with_order behavior).
    let backup: Vec<Poly> = known_gb.iter().chain(new_polys.iter())
        .map(|p| p.clone())
        .collect();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut igb = IncrementalGB::new(ring.clone(), cfg);
        // Seed with the trusted reduced GB. add_generators reduces each input
        // by the current basis before insertion; for a reduced GB this is a
        // no-op, but it generates S-pairs only against EARLIER basis elements
        // (within known_gb). All those S-pairs reduce to zero by Buchberger's
        // criterion (since known_gb is already a GB), so this pass is cheap.
        igb.add_generators(known_gb)?;
        // Now genuinely incremental: only the cross-pairs (known_gb × new) and
        // intra-new pairs are processed.
        igb.add_generators(new_polys)?;
        Ok::<Vec<Poly>, crate::SolverError>(igb.basis())
    }));
    match result {
        Ok(Ok(basis)) => basis,
        Ok(Err(_)) => backup,
        Err(_) => {
            log::warn!("Incremental GB computation panicked; returning concatenated generators unreduced");
            backup
        }
    }
}

/// Traced variant: feeds Buchberger steps to `tracer` for UNSAT-core extraction.
///
/// `tracer` must have been constructed with `n_inputs >= generators.len()` and
/// be in a fresh state (or have been previously fed exactly `tracer.basis_count()`
/// initial-basis events corresponding to earlier generators in the same global
/// input numbering).
pub fn compute_gb_with_order_traced(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::tracer::GbTracer,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_with_order_traced");
    if generators.is_empty() {
        return Vec::new();
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
    };
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        buchberger::groebner_basis_observed(generators, &ring, &cfg, tracer)
    }));
    match result {
        Ok(Ok(GBasis { basis, .. })) => basis,
        Ok(Err(_)) => backup,
        Err(_) => {
            log::warn!("GB computation panicked; returning generators unreduced");
            backup
        }
    }
}

/// Traced incremental variant.  Mirrors `compute_gb_incremental_with_order`
/// but feeds `tracer` with observer events.  The tracer's `n_inputs` must
/// be at least `known_gb.len() + new_polys.len()` for the dependency
/// numbering to remain in-range.
///
/// Each generator pushed to the basis is registered against the tracer
/// in order — first all `known_gb` elements, then all `new_polys` —
/// matching the ordinal used by a fresh `GbTracer`.
pub fn compute_gb_incremental_with_order_traced(
    poly_ring: &FfPolyRing,
    known_gb: Vec<Poly>,
    new_polys: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::tracer::GbTracer,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_incremental_with_order_traced");
    if new_polys.is_empty() {
        return known_gb;
    }
    if known_gb.is_empty() {
        return compute_gb_with_order_traced(poly_ring, new_polys, cancel, order, tracer);
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
    };
    let backup: Vec<Poly> = known_gb.iter().chain(new_polys.iter())
        .map(|p| p.clone())
        .collect();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut igb = IncrementalGB::new(ring.clone(), cfg);
        igb.add_generators_observed(known_gb, tracer)?;
        igb.add_generators_observed(new_polys, tracer)?;
        Ok::<Vec<Poly>, crate::SolverError>(igb.basis())
    }));
    match result {
        Ok(Ok(basis)) => basis,
        Ok(Err(_)) => backup,
        Err(_) => {
            log::warn!("Traced incremental GB computation panicked; returning concatenated generators unreduced");
            backup
        }
    }
}

// Silence dead-code warnings on shim type alias.
#[allow(dead_code)]
type _GbBaseRing<'r> = &'r crate::field::FfFieldType;

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
        // I = (x - 3) over GF(17). Then (x^2 - 9) ∈ I, but x ∉ I.
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
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let one = pr.one();
        let ideal = Ideal::new(&pr, vec![one]);
        assert!(ideal.is_whole_ring());
        assert!(ideal.is_zero_dim());
    }

    #[test]
    fn test_is_zero_dim_yes() {
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
        let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
        let xy = pr.mul(pr.var(0), pr.var(1));
        let ideal = Ideal::new(&pr, vec![xy]);
        assert!(!ideal.is_zero_dim());
    }

    #[test]
    fn test_min_poly_constant_var() {
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let five = pr.field.from_int(5);
        let p1 = pr.sub(pr.var(0), pr.constant(five));
        let ideal = Ideal::new(&pr, vec![p1]);
        let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
        assert_eq!(mp.len(), 2);
        let fp = pr.field.field();
        let neg_five = fp.neg(&pr.field.from_int(5));
        assert!(fp.eq_el(&mp[0], &neg_five));
        assert!(fp.is_one(&mp[1]));
    }

    #[test]
    fn test_min_poly_quadratic() {
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let x = pr.var(0);
        let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let one = pr.one();
        let p = pr.sub(x2, one);
        let ideal = Ideal::new(&pr, vec![p]);
        let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
        assert_eq!(mp.len(), 3);
        let fp = pr.field.field();
        let neg_one = fp.neg(&fp.one());
        assert!(fp.eq_el(&mp[0], &neg_one));
        assert!(fp.is_zero(&mp[1]));
        assert!(fp.is_one(&mp[2]));
    }

    #[test]
    fn test_normalize() {
        let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
        let three = pr.field.from_int(3);
        let six = pr.field.from_int(6);
        let term1 = pr.scale(three, pr.var(0));
        let p = pr.add(term1, pr.constant(six));
        let ideal = Ideal::new(&pr, vec![]);
        let normalized = ideal.normalize(&p);
        let lc = leading_coefficient(&pr.ring, &normalized, FfOrder::DegRevLex);
        assert!(pr.field.field().is_one(&lc));
    }
}
