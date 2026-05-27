//! Gröbner-basis engine front-door for [`super::Ideal`]: the pluggable
//! [`GbAlgorithm`] strategy + dispatch, and the `compute_gb_*` family with
//! its dense/sparse representation routing and the shared `finish_gb`
//! cancel/error/backup contract. Split out of `ideal.rs` so the `Ideal`
//! algebra and the GB computation engine read separately; re-exported from
//! `ideal` so `gb::ideal::compute_gb_with_order` etc. paths are unchanged.

use std::cell::RefCell;

use crate::config::GbStrategy;
use crate::ff::buchberger::{self, BuchbergerConfig, GBasis, IncrementalGB};
use crate::ff::monomial::MonomialOrder as FfOrder;
use crate::gb::tracer::GbTracer;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;
use crate::EngineError;

/// Pluggable Groebner-basis algorithm.
///
/// Every public GB entry point (`compute_gb_with_order` and its
/// traced sibling) routes through [`compute_gb_dispatch`], which
/// selects a strategy from [`crate::config::RuntimeConfig::gb_strategy`]
/// and forwards.
///
/// Scope: this trait dispatches the *algorithm strategy* — currently the
/// homogenisation choice ([`BuchbergerDirect`] vs [`BuchbergerByHomog`]),
/// and the extension point for a genuinely different algorithm such as a
/// signature-based F5. It does **not** select the polynomial
/// representation (dense vs sparse — chosen inside `compute` from
/// `config.poly_repr`) nor the F4 matrix batch path (chosen via
/// `BuchbergerConfig.use_f4`): those are orthogonal implementation
/// choices made within a strategy's `compute`, not separate
/// `GbAlgorithm`s. A CoCoA-style F4 improvement lands in the
/// Buchberger/F4 engine, not as a new trait impl.
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
    let n = pr.n_vars();
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

// ──────────────────── compute_gb_with_order family ────────────────────────

/// Build a per-call `ff::PolyRing` whose monomial order matches `order`.
/// Cheap (an `Arc<PolyRing>` with the same field/var-name data).
pub(crate) fn ring_for_order(poly_ring: &FfPolyRing, order: FfOrder) -> std::sync::Arc<crate::ff::polynomial::PolyRing> {
    crate::ff::polynomial::PolyRing::new(
        poly_ring.field().clone(),
        poly_ring.var_names().to_vec(),
        order,
    )
}

/// True when the configured IR representation is sparse, so native GB
/// computation should be routed through the sparse engine.
#[inline]
pub(crate) fn use_sparse_gb() -> bool {
    crate::config::with(|c| c.poly_repr == crate::config::ReprKind::Sparse)
}

/// Compute a Gröbner basis through the sparse engine (`ff::sparse_gb`)
/// when the ring's representation is sparse: extract each generator's
/// sparse arm, compute and inter-reduce sparsely, and return a sparse-arm
/// basis (the polynomials stay resident-sparse, no dense materialisation).
///
/// Contract (load-bearing, not encoded in the return type): on
/// **cancellation** the sparse engine returns the basis built so far — a
/// valid generating set of the same ideal but NOT a complete Gröbner
/// basis — and this function passes it through, so every caller MUST
/// re-check `cancel.is_cancelled()` and discard it before trusting it as a
/// GB. Unlike the dense path (`compute_gb_buchberger`), there is no
/// `catch_unwind` here: a panic in the sparse engine propagates to the
/// process-level hook (a crash → Unknown, never a false verdict).
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
/// order, routed through [`compute_gb_dispatch`].
///
/// On failure the result depends on the cause:
/// * Cancellation — return the generators unchanged; every caller
///   re-checks `cancel.is_cancelled()` and reports `Timeout`, discarding
///   this value.
/// * Genuine engine error (e.g. a caught panic) — return an *empty*
///   basis. The unreduced generators are not a Gröbner basis, and
///   handing them back would let `is_zero_dim`/`min_poly`/FGLM treat a
///   non-GB as a GB (a possible false UNSAT). An empty basis instead
///   leaves the ideal undetermined downstream (→ Unknown, or a
///   `verify_model`-guarded SAT), never a trusted zero-dimensional GB.
/// Resolve a GB `Result` into a basis under the soundness contract shared
/// by every public GB entry point: on **cancellation** return `backup`
/// (the caller's `is_cancelled()` check then discards it); on a **genuine
/// engine error** return an empty basis — never the unreduced generators,
/// so downstream cannot mistake them for a Gröbner basis and emit a wrong
/// verdict. `what` names the call site for the warning log.
fn finish_gb(
    result: Result<Vec<Poly>, EngineError>,
    cancel: &CancelToken,
    backup: Vec<Poly>,
    what: &str,
) -> Vec<Poly> {
    result.unwrap_or_else(|e| {
        if cancel.is_cancelled() {
            backup
        } else {
            log::warn!("{} failed ({:?}); returning empty basis (Unknown)", what, e);
            Vec::new()
        }
    })
}

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
    let n_vars = poly_ring.n_vars();
    let backup: Vec<Poly> = generators.iter().map(|p| p.clone()).collect();
    let start = std::time::Instant::now();
    let result = compute_gb_dispatch(poly_ring, generators, cancel, order, None);
    let elapsed = start.elapsed();
    let basis = finish_gb(result, cancel, backup, "GB dispatch");
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
/// on cancellation → generators unchanged (caller discards); on a genuine
/// engine error → empty (never a fake GB; see [`compute_gb_with_order`]).
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
    let result = compute_gb_buchberger(poly_ring, generators, cancel, order);
    finish_gb(result, cancel, backup, "inner direct GB")
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

    // Cancellation fallback: the caller discards this via its
    // is_cancelled() check. A genuine engine error returns an empty basis
    // instead (see `compute_gb_with_order`) — never a fake GB.
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
    let result: Result<Vec<Poly>, EngineError> = match result {
        Ok(Ok(basis)) => Ok(wrap_dense_vec(basis)),
        Ok(Err(e)) => Err(e),
        Err(_) => Err(EngineError::Internal("incremental GB panicked".into())),
    };
    finish_gb(result, cancel, backup, "incremental GB")
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
    finish_gb(result, cancel, backup, "traced GB dispatch")
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
        // Mirror `compute_gb_incremental_with_order`: a genuine engine error
        // (panic or non-cancel `Err`) returns an empty basis, never the
        // unreduced `known_gb ++ new_polys`. Handing back a non-GB would let a
        // downstream `is_zero_dim`/`min_poly`/FGLM treat it as a GB (a possible
        // false UNSAT); an empty basis is `is_whole_ring() == false`, so the
        // split-GB fixpoint keeps searching (Unknown) rather than concluding.
        // `backup` is returned only on cooperative cancellation.
        Ok(Err(_)) | Err(_) => {
            if cancel.is_cancelled() {
                backup
            } else {
                log::warn!("traced incremental GB failed; returning empty basis (Unknown)");
                Vec::new()
            }
        }
    }
}

// Silence dead-code warnings on shim type alias.
#[allow(dead_code)]
type _GbBaseRing<'r> = &'r crate::ff::field::PrimeField;
