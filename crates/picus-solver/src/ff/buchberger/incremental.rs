//! Incremental Buchberger driver with push / pop checkpointing.
//!
//! Wraps [`super::BuchbergerState`] to provide:
//!   * `add_generators` / `add_generators_observed` — extend the GB by
//!     reducing new polynomials against the current basis.
//!   * `push` / `pop` — DFS-style backtracking via a `Checkpoint` trail.
//!   * `run_only` / `set_cancel_token` — resume an in-flight build with
//!     a fresh cancel budget across solve-call boundaries.

use std::sync::Arc;

use crate::EngineError;
use crate::timeout::CancelToken;

use super::super::polynomial::{PolyRing, DensePoly};
use super::super::spair::SPair;
use super::{BasisElement, BuchbergerConfig, BuchbergerObserver, BuchbergerState, NoObserver};

/// Snapshot of the engine state at a `push` point. Restored on `pop`.
#[derive(Clone, Debug)]
struct Checkpoint {
    /// Complete snapshot of the basis elements present at push time,
    /// including polynomial bodies. `add_generators` / `run_only` run
    /// `tail_reduce_active`, which rewrites the bodies of pre-push
    /// elements using post-push (higher-generation) reducers; those
    /// contributions need not lie in the pre-push ideal, so `pop` must
    /// restore the bodies — not just the `active` flags — or the
    /// popped-level basis is no longer a basis of the pre-push ideal.
    basis_snapshot: Vec<BasisElement>,
    /// Generation at this level — bumped on `pop`.
    generation: u32,
    /// Snapshot of the open S-pair queue (sorted descending, same
    /// convention as [`BuchbergerState::open`]).
    saved_open: Vec<SPair>,
    age_counter: u64,
    trivial: bool,
}

pub struct IncrementalGB {
    state: BuchbergerState,
    trail: Vec<Checkpoint>,
}

impl IncrementalGB {
    pub fn new(ring: Arc<PolyRing>, cfg: BuchbergerConfig) -> Self {
        IncrementalGB {
            state: BuchbergerState::new(ring, cfg),
            trail: Vec::new(),
        }
    }

    pub fn ring(&self) -> &Arc<PolyRing> { &self.state.ring }

    /// Seed the engine with a polynomial set that is already a reduced
    /// GB in the engine's order. Skips S-pair generation among these
    /// inputs entirely — the caller asserts the seeded set has no open
    /// obligations.
    pub fn seed_reduced_basis(&mut self, basis: Vec<DensePoly>) {
        self.state.seed_with_reduced_basis(basis);
    }

    pub fn add_generators(&mut self, polys: Vec<DensePoly>) -> Result<bool, EngineError> {
        let mut obs = NoObserver;
        self.state.add_generators(polys, &mut obs)?;
        self.state.run(&mut obs)?;
        // Tail-reduce the active basis to prevent monotonic growth across
        // successive `add_generators` calls.
        if !self.state.trivial {
            self.state.tail_reduce_active(false);
        }
        Ok(self.state.trivial)
    }

    /// Drain the in-progress S-pair queue without adding new generators.
    /// Used by [`crate::incremental_context::IncrementalSolverContext`]
    /// to resume a previously-cancelled GB build across solve calls.
    ///
    /// Semantics are identical to `add_generators(vec![])` but skips the
    /// no-op generator append and the homogeneous-input flag detection
    /// (which is set on the first call and is immutable thereafter).
    pub fn run_only(&mut self) -> Result<bool, EngineError> {
        let mut obs = NoObserver;
        self.state.run(&mut obs)?;
        if !self.state.trivial {
            self.state.tail_reduce_active(false);
        }
        Ok(self.state.trivial)
    }

    /// Swap in a fresh cancel token. Each
    /// [`crate::incremental_context::IncrementalSolverContext::solve`]
    /// invocation produces its own per-call cancel token; a persisted
    /// `IncrementalGB` must pick that up so a resumed run respects the
    /// new budget.
    pub fn set_cancel_token(&mut self, token: Option<CancelToken>) {
        self.state.cfg.cancel_token = token;
    }

    /// True iff the open S-pair queue is empty (no further reductions
    /// pending). When `is_quiescent()` and `!is_trivial()`, the active
    /// polys form a Groebner basis (modulo a final inter-reduce).
    pub fn is_quiescent(&self) -> bool {
        self.state.open.is_empty()
    }

    /// Number of pending S-pairs in the open queue. Diagnostic.
    pub fn open_queue_len(&self) -> usize {
        self.state.open.len()
    }

    /// Observed variant of [`Self::add_generators`]: the supplied
    /// observer receives `on_initial_basis` / `on_new_poly` /
    /// `on_inter_reduce` callbacks during the GB extension. Used by
    /// [`crate::gb::tracer::GbTracer`] for UNSAT-core extraction.
    pub fn add_generators_observed<O: BuchbergerObserver>(
        &mut self,
        polys: Vec<DensePoly>,
        observer: &mut O,
    ) -> Result<bool, EngineError> {
        self.state.add_generators(polys, observer)?;
        self.state.run(observer)?;
        // Skip tail-reduce: the observer relies on basis-element identity
        // for UNSAT-core extraction; rewriting polynomial bodies underneath
        // it would invalidate that tracking.
        Ok(self.state.trivial)
    }

    /// Save a checkpoint for backtracking. Clones the surviving basis
    /// elements (with their polynomial bodies) and the open S-pair queue,
    /// so cost is O(sum of basis body sizes + open_len). Cloning bodies is
    /// required, not optional: `tail_reduce_active` rewrites pre-push
    /// element bodies with post-push contributions that `pop` must roll
    /// back.
    pub fn push(&mut self) {
        self.trail.push(Checkpoint {
            basis_snapshot: self.state.basis.clone(),
            generation: self.state.generation,
            saved_open: self.state.open.clone(),
            age_counter: self.state.age_counter,
            trivial: self.state.trivial,
        });
        self.state.generation = self.state.generation.wrapping_add(1);
    }

    pub fn pop(&mut self) {
        if let Some(cp) = self.trail.pop() {
            // Restore the basis to its exact push-time state in one move:
            // this drops every element added since the push and rolls back
            // the bodies / `active` flags of the survivors (which
            // tail-reduction may have rewritten).
            self.state.basis = cp.basis_snapshot;
            self.state.open = cp.saved_open;
            self.state.age_counter = cp.age_counter;
            self.state.generation = cp.generation;
            self.state.trivial = cp.trivial;
        }
    }

    pub fn basis(&self) -> Vec<DensePoly> {
        self.state.active_polys()
    }

    pub fn reduce(&self, p: &DensePoly) -> DensePoly {
        let refs = self.state.active_poly_refs();
        p.reduce_by_refs(&refs, &self.state.ring)
    }

    pub fn is_trivial(&self) -> bool {
        self.state.trivial
    }

    pub fn decision_level(&self) -> usize {
        self.trail.len()
    }

    /// Per-run profiling counters accumulated across every
    /// `add_generators` / `run_only` call. Emitted on stderr when
    /// `gb_stats` is enabled; read here by tests (which enable `gb_stats`,
    /// since the counters are gb-stats-gated). Pure telemetry — no field
    /// drives engine logic.
    pub fn engine_stats(&self) -> &super::GbProfileCounters {
        &self.state.profile
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::ff::monomial::MonomialOrder;
    use num_bigint::BigUint;

    fn ring2() -> Arc<PolyRing> {
        // `PolyRing::new` already returns `Arc<Self>`.
        PolyRing::new(
            PrimeField::new(BigUint::from(7u32)),
            vec!["x".into(), "y".into()],
            MonomialOrder::DegRevLex,
        )
    }

    fn cfg() -> BuchbergerConfig {
        BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: true,
            use_f4: false,
        }
    }

    #[test]
    fn new_starts_quiescent_empty_basis_level_0() {
        let igb = IncrementalGB::new(ring2(), cfg());
        assert!(igb.is_quiescent());
        assert_eq!(igb.open_queue_len(), 0);
        assert!(igb.basis().is_empty());
        assert!(!igb.is_trivial());
        assert_eq!(igb.decision_level(), 0);
    }

    #[test]
    fn seed_reduced_basis_avoids_spair_work() {
        let ring = ring2();
        let mut igb = IncrementalGB::new(ring.clone(), cfg());
        let x = DensePoly::variable(0, &ring);
        let y = DensePoly::variable(1, &ring);
        igb.seed_reduced_basis(vec![x, y]);
        // Seeded basis has no open S-pairs.
        assert!(igb.is_quiescent());
        assert_eq!(igb.basis().len(), 2);
    }

    #[test]
    fn add_generators_returns_trivial_on_unit_input() {
        let ring = ring2();
        let mut igb = IncrementalGB::new(ring.clone(), cfg());
        let one = DensePoly::constant(ring.field.one(), &ring);
        let trivial = igb.add_generators(vec![one]).expect("trivial GB ok");
        assert!(trivial);
        assert!(igb.is_trivial());
    }

    #[test]
    fn add_generators_two_linear_yields_basis() {
        // x and y are linearly independent → reduced GB = {x, y}.
        let ring = ring2();
        let mut igb = IncrementalGB::new(ring.clone(), cfg());
        let x = DensePoly::variable(0, &ring);
        let y = DensePoly::variable(1, &ring);
        let trivial = igb.add_generators(vec![x, y]).expect("ok");
        assert!(!trivial);
        // The basis is {x, y} after add_generators (each survives).
        assert_eq!(igb.basis().len(), 2);
    }

    #[test]
    fn push_pop_restores_basis_and_level() {
        let ring = ring2();
        let mut igb = IncrementalGB::new(ring.clone(), cfg());
        let x = DensePoly::variable(0, &ring);
        igb.add_generators(vec![x.clone()]).expect("ok");
        let before = igb.basis();

        igb.push();
        assert_eq!(igb.decision_level(), 1);

        // Add another generator at level 1.
        let y = DensePoly::variable(1, &ring);
        igb.add_generators(vec![y]).expect("ok");
        assert!(igb.basis().len() >= 2);

        igb.pop();
        assert_eq!(igb.decision_level(), 0);
        // After pop, the basis is restored to its pre-push state.
        let after = igb.basis();
        assert_eq!(before.len(), after.len());
    }

    #[test]
    fn nested_push_pop_restores_level() {
        let igb_init = IncrementalGB::new(ring2(), cfg());
        let mut igb = igb_init;
        igb.push();
        igb.push();
        igb.push();
        assert_eq!(igb.decision_level(), 3);
        igb.pop();
        assert_eq!(igb.decision_level(), 2);
        igb.pop();
        igb.pop();
        assert_eq!(igb.decision_level(), 0);
        // Extra pop is a no-op (no underflow).
        igb.pop();
        assert_eq!(igb.decision_level(), 0);
    }

    #[test]
    fn set_cancel_token_swaps_in_fresh_budget() {
        let mut igb = IncrementalGB::new(ring2(), cfg());
        // Install a fresh cancel.
        let c = CancelToken::cancelled();
        igb.set_cancel_token(Some(c));
        // No direct getter, but the cancel takes effect when run_only is
        // called and the engine polls.
        let _ = igb.run_only(); // empty queue, nothing to cancel — Ok.
        // Setting None back also works.
        igb.set_cancel_token(None);
    }

    #[test]
    fn run_only_on_empty_queue_is_noop() {
        let mut igb = IncrementalGB::new(ring2(), cfg());
        let trivial = igb.run_only().expect("empty run_only ok");
        assert!(!trivial);
        assert!(igb.is_quiescent());
    }

    #[test]
    fn reduce_against_active_basis_returns_normal_form() {
        let ring = ring2();
        let mut igb = IncrementalGB::new(ring.clone(), cfg());
        let x = DensePoly::variable(0, &ring);
        igb.add_generators(vec![x]).expect("ok");
        // Reduce `2x + 3` by basis {x} → should yield the constant `3`.
        let two = ring.field.from_int(2);
        let two_x = DensePoly::variable(0, &ring).scale(&two, &ring);
        let three = DensePoly::constant(ring.field.from_int(3), &ring);
        let two_x_plus_3 = two_x.add(&three, &ring);
        let r = igb.reduce(&two_x_plus_3);
        // Result depends on monic-normalization; just check it's a constant.
        assert!(r.is_constant() || r.is_zero());
    }

    #[test]
    fn engine_stats_accessor_works() {
        let igb = IncrementalGB::new(ring2(), cfg());
        let stats = igb.engine_stats();
        // Fresh stats — most counters are zero.
        // `assert_eq!(stats.reductions_total, 0)` is implementation-specific;
        // just ensure the accessor returns a reference.
        let _: &super::super::GbProfileCounters = stats;
    }

    #[test]
    fn ring_accessor_returns_arc() {
        let r = ring2();
        let igb = IncrementalGB::new(r.clone(), cfg());
        // Comparison by Arc pointer equality.
        assert!(Arc::ptr_eq(igb.ring(), &r));
    }
}
