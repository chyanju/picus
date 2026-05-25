//! Incremental Buchberger driver with push / pop checkpointing.
//!
//! Wraps [`super::BuchbergerState`] to provide:
//!   * `add_generators` / `add_generators_observed` — extend the GB by
//!     reducing new polynomials against the current basis.
//!   * `push` / `pop` — DFS-style backtracking via a `Checkpoint` trail.
//!   * `run_only` / `set_cancel_token` — resume an in-flight build with
//!     a fresh cancel budget across solve-call boundaries.

use std::sync::Arc;

use crate::SolverError;
use crate::timeout::CancelToken;

use super::super::polynomial::{PolyRing, DensePoly};
use super::super::spair::SPair;
use super::{BuchbergerConfig, BuchbergerObserver, BuchbergerState, NoObserver};

/// Snapshot of the engine state at a `push` point. Restored on `pop`.
#[derive(Clone, Debug)]
struct Checkpoint {
    basis_len: usize,
    /// `active` flags for the elements that existed at push time, so any
    /// deactivations between push and pop are reverted on pop.
    active_snapshot: Vec<bool>,
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

    pub fn add_generators(&mut self, polys: Vec<DensePoly>) -> Result<bool, SolverError> {
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
    pub fn run_only(&mut self) -> Result<bool, SolverError> {
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
    ) -> Result<bool, SolverError> {
        self.state.add_generators(polys, observer)?;
        self.state.run(observer)?;
        // Skip tail-reduce: the observer relies on basis-element identity
        // for UNSAT-core extraction; rewriting polynomial bodies underneath
        // it would invalidate that tracking.
        Ok(self.state.trivial)
    }

    /// Save a checkpoint for backtracking. Cost: O(basis_len + open_len)
    /// (clones the S-pair vector — already sorted, no extra ordering work).
    pub fn push(&mut self) {
        let active_snapshot: Vec<bool> = self.state.basis.iter().map(|e| e.active).collect();
        self.trail.push(Checkpoint {
            basis_len: self.state.basis.len(),
            active_snapshot,
            generation: self.state.generation,
            saved_open: self.state.open.clone(),
            age_counter: self.state.age_counter,
            trivial: self.state.trivial,
        });
        self.state.generation = self.state.generation.wrapping_add(1);
    }

    pub fn pop(&mut self) {
        if let Some(cp) = self.trail.pop() {
            self.state.basis.truncate(cp.basis_len);
            for (idx, was_active) in cp.active_snapshot.into_iter().enumerate() {
                if idx < self.state.basis.len() {
                    self.state.basis[idx].active = was_active;
                }
            }
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

    /// Engine-level counters accumulated across every
    /// `add_generators` / `run_only` call. Same data emitted on
    /// stderr when `gb_stats` is enabled, exposed here for tests.
    pub fn engine_stats(&self) -> &super::GbEngineStats {
        &self.state.stats
    }
}
