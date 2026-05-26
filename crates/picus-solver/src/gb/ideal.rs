//! Ideal operations over GF(p)[x_1, ..., x_n].
//!
//! Thin shim over the in-tree [`crate::ff`] Buchberger / Ideal
//! implementation. Public API: [`Ideal`], [`compute_gb_with_order`],
//! [`compute_gb_with_order_traced`], [`interreduce_basis`],
//! [`leading_monomial`], [`leading_coefficient`],
//! [`GbAlgorithm`], [`last_dispatched_algorithm`].

use std::cell::RefCell;
use std::collections::HashSet;

use crate::ff::buchberger::{
    self, poly_coefficient_at, BuchbergerConfig, GBasis, IncrementalGB,
};
use crate::ff::polynomial::Polynomial;
use crate::ff::monomial::Monomial;
use crate::ff::monomial::MonomialOrder as FfOrder;
use crate::ff::field::FieldElem;
use crate::poly::{FfPolyRing, Mono, Poly, PolyRingType};
use crate::timeout::{CancelToken, Cancelled};
use crate::gb::tracer::GbTracer;
use crate::EngineError;
use crate::config::GbStrategy;

/// Pluggable Groebner-basis algorithm.
///
/// Every public GB entry point (`compute_gb_with_order` and its
/// traced sibling) routes through [`compute_gb_dispatch`], which
/// selects an algorithm from [`crate::config::RuntimeConfig::gb_strategy`]
/// and forwards. Adding a new algorithm (F5, signature-based, CoCoA-
/// style, …) is therefore a matter of implementing this trait and
/// teaching dispatch about it; no other entry point needs touching.
///
/// Two execution modes are supported. `compute` is the basic call;
/// `compute_traced` feeds a [`GbTracer`] observer for UNSAT-core
/// extraction. Algorithms that don't support tracing leave
/// `supports_tracing` at its default `false`; dispatch then falls back
/// to [`BuchbergerDirect`] for traced requests so UNSAT-core extraction
/// keeps working regardless of the configured strategy.
pub trait GbAlgorithm {
    /// Stable name for logs / telemetry.
    fn name(&self) -> &'static str;

    /// Compute a Groebner basis of `<gens>` over `pr` in `order`.
    /// Honours `cancel` for cooperative time limits.
    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError>;

    /// Whether this algorithm implements [`Self::compute_traced`].
    fn supports_tracing(&self) -> bool {
        false
    }

    /// Traced variant. Only called when `supports_tracing()` is
    /// `true`. The default implementation panics — implementors that
    /// flip `supports_tracing` to `true` must override this method.
    fn compute_traced(
        &self,
        _pr: &FfPolyRing,
        _gens: Vec<Poly>,
        _cancel: &CancelToken,
        _order: FfOrder,
        _tracer: &mut GbTracer,
    ) -> Result<Vec<Poly>, EngineError> {
        unreachable!(
            "GbAlgorithm {:?}: supports_tracing() returned true but \
             compute_traced is the default panicking impl",
            self.name()
        )
    }
}

/// Plain Buchberger on `P` in the requested order. The default.
pub struct BuchbergerDirect;

impl GbAlgorithm for BuchbergerDirect {
    fn name(&self) -> &'static str {
        "buchberger-direct"
    }

    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError> {
        compute_gb_buchberger(pr, gens, cancel, order)
    }

    fn supports_tracing(&self) -> bool {
        true
    }

    fn compute_traced(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
        tracer: &mut GbTracer,
    ) -> Result<Vec<Poly>, EngineError> {
        compute_gb_buchberger_traced(pr, gens, cancel, order, tracer)
    }
}

/// Homogenise → Buchberger on `P[h]` (DegRevLex) → dehomogenise →
/// interreduce. Wins on bit-decomposition shaped ideals where sugar
/// mis-prediction stalls the direct path.
///
/// Only meaningful for `DegRevLex` requests. Lex / other orders fall
/// back to plain `BuchbergerDirect` for that call.
pub struct BuchbergerByHomog;

impl GbAlgorithm for BuchbergerByHomog {
    fn name(&self) -> &'static str {
        "buchberger-by-homog"
    }

    fn compute(
        &self,
        pr: &FfPolyRing,
        gens: Vec<Poly>,
        cancel: &CancelToken,
        order: FfOrder,
    ) -> Result<Vec<Poly>, EngineError> {
        if order == FfOrder::DegRevLex {
            Ok(crate::gb::gb_homog::compute_gb_by_homog(pr, gens, cancel))
        } else {
            // ByHomog only makes sense for DegRevLex; for Lex etc.
            // route through plain Buchberger so the contract of
            // returning a basis in `order` holds.
            BuchbergerDirect.compute(pr, gens, cancel, order)
        }
    }
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

thread_local! {
    /// Name of the most recent GB algorithm chosen by [`compute_gb_dispatch`]
    /// on this thread. Used by tests to confirm dispatch is actually
    /// honouring the configured strategy.
    static LAST_DISPATCHED: RefCell<Option<&'static str>> = const { RefCell::new(None) };
}

/// Name of the algorithm that last serviced a GB request on the current
/// thread, or `None` if no GB call has run yet. The dense path records the
/// dispatched [`GbAlgorithm`] (`"buchberger-direct"` / `"buchberger-by-homog"`);
/// the sparse path records `"sparse-buchberger"` / `"sparse-by-homog"`.
pub fn last_dispatched_algorithm() -> Option<&'static str> {
    LAST_DISPATCHED.with(|c| *c.borrow())
}

fn record_dispatched(name: &'static str) {
    LAST_DISPATCHED.with(|c| *c.borrow_mut() = Some(name));
}

/// Pick the configured [`GbAlgorithm`] and run it. When `tracer` is
/// `Some` but the chosen algorithm cannot honour tracing, falls back
/// to [`BuchbergerDirect`] so UNSAT-core extraction continues to work.
fn compute_gb_dispatch(
    pr: &FfPolyRing,
    gens: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: Option<&mut GbTracer>,
) -> Result<Vec<Poly>, EngineError> {
    if gens.is_empty() {
        return Ok(Vec::new());
    }
    let strat = match crate::config::with(|c| c.gb_strategy) {
        GbStrategy::Auto => resolve_auto(pr, &gens),
        s => s,
    };
    let direct = BuchbergerDirect;
    let by_homog = BuchbergerByHomog;
    let chosen: &dyn GbAlgorithm = match strat {
        GbStrategy::Direct => &direct,
        GbStrategy::ByHomog => &by_homog,
        GbStrategy::Auto => unreachable!("Auto resolved above"),
    };
    match tracer {
        None => {
            record_dispatched(chosen.name());
            chosen.compute(pr, gens, cancel, order)
        }
        Some(t) => {
            if chosen.supports_tracing() {
                record_dispatched(chosen.name());
                chosen.compute_traced(pr, gens, cancel, order, t)
            } else {
                // Drop down to Direct to preserve UNSAT-core extraction.
                if chosen.name() != direct.name() {
                    log::debug!(
                        "GbAlgorithm {:?} does not support tracing; falling back to {:?}",
                        chosen.name(), direct.name()
                    );
                }
                record_dispatched(direct.name());
                direct.compute_traced(pr, gens, cancel, order, t)
            }
        }
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
        // Delegates to the cancel-aware variant with a never-firing
        // token so both entry points produce identical bases
        // (including the `interreduce_basis` pass after Buchberger's
        // internal finalisation). The `Err` arm is unreachable with
        // a never-firing token; the empty-ideal fallback keeps `new`
        // total.
        Self::new_with_cancel(poly_ring, generators, &CancelToken::none())
            .unwrap_or_else(|_| Ideal { poly_ring, basis: Vec::new() })
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
        let basis = compute_gb_dispatch(
            poly_ring, generators, cancel, FfOrder::DegRevLex, None,
        )
        .map_err(|_| Cancelled)?;
        if cancel.is_cancelled() { return Err(Cancelled); }
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Extend an existing ideal by adding new generators incrementally.
    ///
    /// Reuses the existing reduced GB and runs incremental Buchberger
    /// seeded with the existing basis, computing only cross / intra
    /// S-pairs involving the new generators. The final GB equals the
    /// one obtained by full recomputation on the union of generators.
    pub(crate) fn extend_with_cancel(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        if crate::profile::gb_stats_enabled() {
            crate::profile::SPLIT_GB.extend_with_cancel_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !f.is_zero())
            .collect();
        if new_polys.is_empty() {
            if crate::profile::gb_stats_enabled() {
                crate::profile::SPLIT_GB.extend_no_op_skips
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            return Ok(self);
        }
        // Pre-reduce new generators against the existing reduced GB.
        // If every new polynomial reduces to zero, the ideal is unchanged
        // and the entire incremental Buchberger + interreduce round-trip
        // can be skipped.
        let surviving: Vec<Poly> = if self.basis.is_empty() {
            new_polys
        } else {
            let basis_refs: Vec<&Poly> = self.basis.iter().collect();
            let ring = self.poly_ring.ctx();
            new_polys.into_iter()
                .map(|p| p.reduce_by_refs_cancel(&basis_refs, ring, cancel))
                .filter(|p| !p.is_zero())
                .collect()
        };
        if cancel.is_cancelled() { return Err(Cancelled); }
        if surviving.is_empty() {
            if crate::profile::gb_stats_enabled() {
                crate::profile::SPLIT_GB.extend_no_op_skips
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order(
            poly_ring, known_gb, surviving, cancel, FfOrder::DegRevLex,
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
    pub(crate) fn extend_with_cancel_traced(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
        tracer: &mut crate::gb::tracer::GbTracer,
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

    /// Cancel-aware reduce. On cancel returns whatever partial remainder
    /// the geobucket reducer had accumulated — sound (still represents the
    /// same residue class) but not a normal form, so callers that want
    /// `is_zero` membership semantics must check `cancel.is_cancelled()`
    /// themselves to distinguish "really not in I" from "ran out of time."
    pub fn reduce_with_cancel(&self, p: &Poly, cancel: &CancelToken) -> Poly {
        if self.basis.is_empty() {
            return p.clone();
        }
        let ring = self.poly_ring.ctx();
        let refs: Vec<&Poly> = self.basis.iter().collect();
        p.reduce_by_refs_cancel(&refs, ring, cancel)
    }

    /// Ideal membership: returns `true` iff `p ∈ I`.
    pub fn contains(&self, p: &Poly) -> bool {
        self.reduce(p).is_zero()
    }

    /// Cancel-aware membership test. On cancel returns the value computed
    /// from a partial reduction, which may falsely report "not in I" if
    /// cancellation interrupts mid-reduce. Callers should treat a `false`
    /// result with a cancelled token as "unknown, please retry / abort".
    pub fn contains_with_cancel(&self, p: &Poly, cancel: &CancelToken) -> bool {
        self.reduce_with_cancel(p, cancel).is_zero()
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

    /// `dim_k(R/I)` — the number of standard monomials, equivalently the
    /// number of solutions of `I` with multiplicity over the algebraic
    /// closure — read off the leading monomials of this basis via the
    /// Hilbert function ([`crate::ff::hilbert::quotient_dimension`]).
    ///
    /// `Some(0)` for the whole ring, `Some(d)` for a zero-dimensional ideal,
    /// `None` when `R/I` is not finite-dimensional (positive-dimensional) or
    /// the dimension is declined for a pathologically large ideal. A pure
    /// combinatorial read of the finished basis (sound, verdict-neutral);
    /// cross-checks the FGLM staircase size in [`crate::gb::fglm`].
    pub fn quotient_dimension(&self) -> Option<u128> {
        if self.is_whole_ring() {
            return Some(0);
        }
        if self.basis.is_empty() {
            return None;
        }
        let ring = self.poly_ring.ctx();
        let n_vars = self.poly_ring.n_vars;
        let mut lead: Vec<Monomial> = Vec::with_capacity(self.basis.len());
        for p in &self.basis {
            if p.is_zero() {
                continue;
            }
            if let Some(lm) = p.leading_monomial(ring) {
                lead.push(lm);
            }
        }
        crate::ff::hilbert::quotient_dimension(&lead, n_vars)
    }

    /// Compute the minimal polynomial of `var_idx` in `R/I`.
    pub fn min_poly(&self, var_idx: usize) -> Option<Vec<FieldElem>> {
        self.min_poly_cancel(var_idx, &CancelToken::none())
    }

    /// Cancel-aware variant of [`Self::min_poly`].
    ///
    /// Computes the monic minimal polynomial of `x_{var_idx}` in `R/I`
    /// via Gaussian elimination on the normal forms of `1, x, x^2, ...`.
    /// Returns `None` if the ideal is not zero-dimensional or the search
    /// hits the degree cap.
    pub fn min_poly_cancel(&self, var_idx: usize, cancel: &CancelToken) -> Option<Vec<FieldElem>> {
        let _t = crate::profile::ScopedTimer::new("ideal::min_poly");
        let ring = self.poly_ring.ctx();
        let f = &ring.field;
        if self.is_whole_ring() { return Some(vec![f.one()]); }
        if !self.is_zero_dim() { return None; }

        let one_poly = Polynomial::constant(f.one(), ring);
        let x_poly = Polynomial::variable(var_idx, ring);
        let one_nf = self.reduce(&one_poly);
        let mut powers: Vec<Polynomial> = vec![one_nf];

        const MIN_POLY_DEG_CAP: usize = 4096;

        // Echelon form: each row is (normal_form, dependency vector).
        let mut nfs: Vec<Polynomial> = Vec::new();
        let mut deps: Vec<Vec<FieldElem>> = Vec::new();
        let mut pivot_monos: Vec<Monomial> = Vec::new();

        for d in 0..=MIN_POLY_DEG_CAP {
            if cancel.is_cancelled() { return None; }
            let nf = if d == 0 {
                powers[0].clone()
            } else {
                let prev = powers[d - 1].clone();
                let next = prev.mul(&x_poly, ring);
                self.reduce(&next)
            };
            if d > 0 {
                powers.push(nf.clone());
            }

            // Build a row: (nf, e_d).
            let mut row_poly = nf.clone();
            let mut row_dep: Vec<FieldElem> = vec![f.zero(); d + 1];
            row_dep[d] = f.one();

            // Reduce row against existing echelon rows.
            for (i, nf_i) in nfs.iter().enumerate() {
                let lm_i = &pivot_monos[i];
                let coeff_at_lm = poly_coefficient_at(row_poly.as_dense(ring).as_ref(), lm_i, ring);
                if !f.is_zero(&coeff_at_lm) {
                    let lc_i = poly_coefficient_at(nf_i.as_dense(ring).as_ref(), lm_i, ring);
                    debug_assert!(!f.is_zero(&lc_i));
                    let factor = f.div(&coeff_at_lm, &lc_i).unwrap();
                    let neg_factor = f.neg(&factor);
                    let scaled = nf_i.scale(&neg_factor, ring);
                    row_poly = row_poly.add(&scaled, ring);
                    let dep_i = &deps[i];
                    debug_assert!(dep_i.len() <= row_dep.len(),
                        "echelon row dep length exceeds current row_dep");
                    for k in 0..dep_i.len() {
                        let prod = f.mul(&factor, &dep_i[k]);
                        f.sub_assign(&mut row_dep[k], &prod);
                    }
                }
            }

            if row_poly.is_zero() {
                // Found a dependency: normalise so the leading coefficient is 1.
                let mut top = row_dep.len();
                while top > 0 && f.is_zero(&row_dep[top - 1]) { top -= 1; }
                if top == 0 { return Some(vec![f.one()]); }
                let lead = row_dep[top - 1].clone();
                let mut coeffs: Vec<FieldElem> = Vec::with_capacity(top);
                for k in 0..top {
                    coeffs.push(f.div(&row_dep[k], &lead).unwrap());
                }
                return Some(coeffs);
            }

            // Add to echelon: pivot is the leading monomial of the (reduced) row.
            if let Some(lm) = row_poly.leading_monomial(ring) {
                pivot_monos.push(lm);
                nfs.push(row_poly);
                deps.push(row_dep);
            }
        }
        None
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
) -> FieldElem {
    match p.leading_coefficient() {
        Some(c) => ring.field().clone_el(c),
        None => ring.field().zero(),
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
    if use_sparse_gb() {
        let ctx = poly_ring.ctx();
        let sparse: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
            basis.iter().map(|p| p.to_sparse(ctx)).collect();
        let reduced = crate::ff::sparse_gb::interreduce(sparse, ctx, Some(cancel));
        return reduced.into_iter().map(Poly::Sparse).collect();
    }
    wrap_dense_vec(buchberger::interreduce_with_cancel(
        unwrap_dense_vec(basis, poly_ring.ctx()),
        poly_ring.ctx(),
        Some(cancel),
    ))
}

// ──────────────────── compute_gb_with_order family ────────────────────────

/// Build a per-call `ff::PolyRing` whose monomial order matches `order`.
/// Cheap (an `Arc<PolyRing>` with the same field/var-name data).
pub(crate) fn ring_for_order(poly_ring: &FfPolyRing, order: FfOrder) -> std::sync::Arc<crate::ff::polynomial::PolyRing> {
    crate::ff::polynomial::PolyRing::new(
        poly_ring.field.clone(),
        poly_ring.var_names.clone(),
        order,
    )
}

/// True when the configured IR representation is sparse, so native GB
/// computation should be routed through the sparse engine.
#[inline]
fn use_sparse_gb() -> bool {
    crate::config::with(|c| c.poly_repr == crate::config::ReprKind::Sparse)
}

/// Compute a Gröbner basis through the sparse engine (`ff::sparse_gb`)
/// when the ring's representation is sparse: extract each generator's
/// sparse arm, compute and inter-reduce sparsely, and return a sparse-arm
/// basis (the polynomials stay resident-sparse, no dense materialisation).
fn sparse_gb_route(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    order: FfOrder,
    cancel: &CancelToken,
) -> Vec<Poly> {
    let ring = ring_for_order(poly_ring, order);
    let sparse: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
        generators.iter().map(|p| p.to_sparse(&ring)).collect();
    let gb = crate::ff::sparse_gb::groebner_basis(sparse, &ring, Some(cancel));
    let reduced = crate::ff::sparse_gb::interreduce(gb, &ring, Some(cancel));
    reduced.into_iter().map(Poly::Sparse).collect()
}

/// Unwrap a vector of solve-core `Poly` to the dense `DensePoly` the
/// Gröbner engine consumes. On the dense path every element is already
/// the `Dense` arm; a stray sparse element is materialised to dense.
pub(crate) fn unwrap_dense_vec(v: Vec<Poly>, ring: &crate::ff::polynomial::PolyRing) -> Vec<crate::ff::DensePoly> {
    v.into_iter()
        .map(|p| match p {
            Poly::Dense(d) => d,
            Poly::Sparse(s) => s.to_dense(ring),
        })
        .collect()
}

/// Wrap dense engine output back into solve-core `Poly`.
pub(crate) fn wrap_dense_vec(v: Vec<crate::ff::DensePoly>) -> Vec<Poly> {
    v.into_iter().map(Poly::Dense).collect()
}

/// Compute a Groebner basis of `generators` in the requested monomial
/// order, routed through [`compute_gb_dispatch`]. Falls back to the
/// unreduced generators on cancellation or panic so callers can
/// proceed in best-effort mode.
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
    if use_sparse_gb() {
        // Honour the configured strategy on the sparse path too: ByHomog
        // (DegRevLex only, mirroring BuchbergerByHomog) runs the
        // homogenize → GB → dehomogenize pipeline with a sparse inner GB;
        // everything else is plain sparse Buchberger.
        let strat = match crate::config::with(|c| c.gb_strategy) {
            GbStrategy::Auto => resolve_auto(poly_ring, &generators),
            s => s,
        };
        if strat == GbStrategy::ByHomog && order == FfOrder::DegRevLex {
            record_dispatched("sparse-by-homog");
            return crate::gb::gb_homog::compute_gb_by_homog(poly_ring, generators, cancel);
        }
        record_dispatched("sparse-buchberger");
        return sparse_gb_route(poly_ring, generators, order, cancel);
    }
    let n_gens = generators.len();
    let n_vars = poly_ring.n_vars;
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();
    let start = std::time::Instant::now();
    let result = compute_gb_dispatch(poly_ring, generators, cancel, order, None);
    let elapsed = start.elapsed();
    let basis = result.unwrap_or_else(|e| {
        log::debug!(
            "GB dispatch returned {:?}; falling back to unreduced generators",
            e
        );
        backup
    });
    log::trace!(
        "GB call: {} gens, {} vars → {} basis elems in {:.1}ms",
        n_gens, n_vars, basis.len(), elapsed.as_secs_f64() * 1000.0
    );
    basis
}

/// Raw Buchberger entry point. Bypasses [`compute_gb_dispatch`] and
/// is used by algorithm implementations themselves (e.g.
/// `BuchbergerByHomog` calls this from its inner GB step on `P[h]`).
/// External callers should prefer [`compute_gb_with_order`].
pub(crate) fn compute_gb_buchberger(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> Result<Vec<Poly>, EngineError> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_buchberger");
    if generators.is_empty() {
        return Ok(Vec::new());
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
        use_f4: crate::ff::buchberger::use_f4_default(),
    };
    let dense_gens = unwrap_dense_vec(generators, &ring);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        buchberger::groebner_basis(dense_gens, &ring, &cfg)
    }));
    match result {
        Ok(Ok(GBasis { basis, .. })) => Ok(wrap_dense_vec(basis)),
        Ok(Err(e)) => Err(e),
        Err(_) => {
            log::warn!("GB computation panicked");
            Err(EngineError::Internal("Buchberger panicked".into()))
        }
    }
}

/// Raw *direct* Gröbner basis (plain Buchberger, no strategy dispatch) on
/// `poly_ring`, routed to the sparse or dense engine per the active
/// representation. The inner homogeneous-GB step of the by-homog pipeline
/// uses this so it never re-enters strategy dispatch. Empty input → empty;
/// on a dense-engine error, falls back to the unreduced generators.
pub(crate) fn compute_gb_direct(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
) -> Vec<Poly> {
    if generators.is_empty() {
        return Vec::new();
    }
    if use_sparse_gb() {
        return sparse_gb_route(poly_ring, generators, order, cancel);
    }
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();
    compute_gb_buchberger(poly_ring, generators, cancel, order).unwrap_or_else(|e| {
        log::debug!("inner direct GB returned {:?}; falling back to unreduced", e);
        backup
    })
}

/// Incremental GB extension. Computes GB of `<known_gb> + <new_polys>`
/// using `known_gb` as a trusted reduced GB seed: S-pairs internal to
/// `known_gb` are skipped (Buchberger criterion), and only S-pairs
/// between `known_gb` × `new_polys` and among `new_polys` themselves
/// are generated and discharged.
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
    if use_sparse_gb() {
        // Incremental seeding: trust `known_gb` as a reduced GB (the same
        // contract the dense path relies on via `seed_reduced_basis`) and
        // process only the cross / intra-new S-pairs, then inter-reduce —
        // identical to recomputing the union, but skips the O(n²) seed
        // pairs.
        let ring = ring_for_order(poly_ring, order);
        let known: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
            known_gb.iter().map(|p| p.to_sparse(&ring)).collect();
        let fresh: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
            new_polys.iter().map(|p| p.to_sparse(&ring)).collect();
        let gb = crate::ff::sparse_gb::groebner_basis_incremental(known, fresh, &ring, Some(cancel));
        let reduced = crate::ff::sparse_gb::interreduce(gb, &ring, Some(cancel));
        return reduced.into_iter().map(Poly::Sparse).collect();
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
        // Incremental extends are tiny-batch (a few new S-pairs per call), so
        // F4's degree-batched matrix never amortizes; run the per-pair engine
        // here. F4 (when enabled) is used only for from-scratch GB.
        // Result-identical (F4 ≡ per-pair).
        use_f4: false,
    };

    // Backup for panic / error fallback (matches compute_gb_with_order behavior).
    let backup: Vec<Poly> = known_gb.iter().chain(new_polys.iter())
        .map(|p| p.clone())
        .collect();

    let dense_known = unwrap_dense_vec(known_gb, &ring);
    let dense_new = unwrap_dense_vec(new_polys, &ring);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut igb = IncrementalGB::new(ring.clone(), cfg);
        // Seed with the trusted reduced GB via the pair-free fast path.
        // `add_generators` would have generated O(n²) S-pairs among the
        // seeded elements (each of which then walks the M-criterion list,
        // O(n³)/O(n⁴) total); since the seed is already a reduced GB,
        // every one of those pairs reduces to zero by Buchberger's
        // criterion. We skip them entirely.
        igb.seed_reduced_basis(dense_known);
        // Genuinely incremental: only the cross-pairs (known_gb × new) and
        // intra-new pairs are processed by add_generators below.
        igb.add_generators(dense_new)?;
        Ok::<Vec<crate::ff::DensePoly>, crate::EngineError>(igb.basis())
    }));
    match result {
        Ok(Ok(basis)) => wrap_dense_vec(basis),
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
/// Traced sibling of [`compute_gb_with_order`]. Routes through
/// [`compute_gb_dispatch`] with `Some(tracer)`; if the dispatched
/// algorithm doesn't support tracing, dispatch silently falls back
/// to [`BuchbergerDirect`] for that call.
pub fn compute_gb_with_order_traced(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::gb::tracer::GbTracer,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_with_order_traced");
    if generators.is_empty() {
        return Vec::new();
    }
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();
    let result = compute_gb_dispatch(poly_ring, generators, cancel, order, Some(tracer));
    result.unwrap_or_else(|e| {
        log::debug!(
            "traced GB dispatch returned {:?}; falling back to unreduced generators",
            e
        );
        backup
    })
}

/// Raw traced Buchberger entry point. Counterpart to
/// [`compute_gb_buchberger`]. Used by [`BuchbergerDirect::compute_traced`]
/// and by future algorithms that opt into tracing.
pub(crate) fn compute_gb_buchberger_traced(
    poly_ring: &FfPolyRing,
    generators: Vec<Poly>,
    cancel: &CancelToken,
    order: FfOrder,
    tracer: &mut crate::gb::tracer::GbTracer,
) -> Result<Vec<Poly>, EngineError> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_buchberger_traced");
    if generators.is_empty() {
        return Ok(Vec::new());
    }
    let ring = ring_for_order(poly_ring, order);
    let cfg = BuchbergerConfig {
        order,
        cancel_token: Some(cancel.clone()),
        abort_on_trivial: true,
        use_f4: crate::ff::buchberger::use_f4_default(),
    };
    let dense_gens = unwrap_dense_vec(generators, &ring);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        buchberger::groebner_basis_observed(dense_gens, &ring, &cfg, tracer)
    }));
    match result {
        Ok(Ok(GBasis { basis, .. })) => Ok(wrap_dense_vec(basis)),
        Ok(Err(e)) => Err(e),
        Err(_) => {
            log::warn!("traced GB computation panicked");
            Err(EngineError::Internal("traced Buchberger panicked".into()))
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
    tracer: &mut crate::gb::tracer::GbTracer,
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
        // See `compute_gb_incremental_with_order`: incremental extends are
        // tiny-batch, so F4 never amortizes — always per-pair here.
        use_f4: false,
    };
    let backup: Vec<Poly> = known_gb.iter().chain(new_polys.iter())
        .map(|p| p.clone())
        .collect();
    let dense_known = unwrap_dense_vec(known_gb, &ring);
    let dense_new = unwrap_dense_vec(new_polys, &ring);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut igb = IncrementalGB::new(ring.clone(), cfg);
        igb.add_generators_observed(dense_known, tracer)?;
        igb.add_generators_observed(dense_new, tracer)?;
        Ok::<Vec<crate::ff::DensePoly>, crate::EngineError>(igb.basis())
    }));
    match result {
        Ok(Ok(basis)) => wrap_dense_vec(basis),
        Ok(Err(_)) => backup,
        Err(_) => {
            log::warn!("Traced incremental GB computation panicked; returning concatenated generators unreduced");
            backup
        }
    }
}

// Silence dead-code warnings on shim type alias.
#[allow(dead_code)]
type _GbBaseRing<'r> = &'r crate::ff::field::PrimeField;

#[cfg(test)]
mod tests;
