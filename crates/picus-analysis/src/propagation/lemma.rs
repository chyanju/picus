//! Propagation lemma plugin interface.
//!
//! Each lemma lives in its own file under `propagation/`, implements
//! [`PropagationLemma`], and submits a [`LemmaDescriptor`] via
//! `inventory::submit!`. The DPVL outer loop discovers descriptors from
//! the inventory registry, instantiates the lemmas selected by the
//! caller's [`crate::dpvl::LemmaSet`], and runs them to a fixed point.
//!
//! Contract:
//! - `run` is called once per outer iteration with a read-only view of
//!   the IR and a mutable [`PropagationCtx`]. The lemma returns `true`
//!   iff it learned something this call (added a known signal,
//!   tightened a range, pushed an equality, or pushed a disjunction).
//! - Constraints pushed to `ctx.learned` (and disjunctions pushed to
//!   `ctx.learned_disjunctions`) are folded into the IR only at the
//!   *end* of an outer iteration, so within a single iteration every
//!   lemma sees the same IR snapshot. Inter-lemma ordering is
//!   therefore irrelevant: the next iteration begins with everyone's
//!   learned facts merged.
//! - Lemmas may carry per-run state on `&mut self` (e.g. caches built
//!   on the first call). Each lemma instance is fresh per DPVL run.
//!   Caches indexed by polynomial position should invalidate when
//!   `ir.equalities.len()` grows — the DPVL driver appends to that
//!   vector after every iteration.

use std::collections::{HashMap, HashSet};

use picus_smt::poly_ir::PolyIR;
use picus_core::poly::IrPoly as Poly;

use crate::propagation::range::RangeValue;

/// Per-iteration mutable state visible to every lemma.
///
/// * `known` / `unknown` partition the wires.
/// * `ranges` carries finite-set constraints (e.g. `{0, 1}` after
///   binary01 fires).
/// * `learned` is the out-buffer for new polynomial equalities; the
///   driver appends them to `ir.equalities` at iteration end.
/// * `learned_disjunctions` is the out-buffer for new
///   `(p_1 = 0 ∨ p_2 = 0 ∨ ...)` clauses; the driver appends them to
///   `ir.disjunctions` at iteration end. Future range-propagation /
///   bit-blasting / cardinality lemmas write here.
pub struct PropagationCtx<'a> {
    pub known: &'a mut HashSet<usize>,
    pub unknown: &'a mut HashSet<usize>,
    pub ranges: &'a mut HashMap<usize, RangeValue>,
    pub learned: &'a mut Vec<Poly>,
    pub learned_disjunctions: &'a mut Vec<Vec<Poly>>,
}

/// Plugin interface for a single propagation lemma.
pub trait PropagationLemma: Send {
    /// Stable name used by the CLI `--lemmas` flag and by tests.
    fn name(&self) -> &'static str;

    /// Run one pass. Returns `true` iff it made progress this call.
    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool;
}

/// Factory closure that builds a fresh lemma instance.
pub type LemmaFactory = fn() -> Box<dyn PropagationLemma>;

/// Inventory entry for a lemma. Submitted via `inventory::submit!`
/// from each lemma's module; collected at link time so a downstream
/// crate can ship its own lemma by linking against picus-analysis and
/// calling `inventory::submit!` on its own descriptor.
pub struct LemmaDescriptor {
    pub name: &'static str,
    pub factory: LemmaFactory,
}

inventory::collect!(LemmaDescriptor);

/// All lemmas discovered via the inventory registry, sorted by name
/// so execution order is reproducible across runs.
pub fn all_descriptors() -> Vec<&'static LemmaDescriptor> {
    let mut v: Vec<&LemmaDescriptor> = inventory::iter::<LemmaDescriptor>.into_iter().collect();
    v.sort_by_key(|d| d.name);
    v
}

/// All registered lemma names, sorted. Used by `LemmaSet::parse` to
/// validate `--lemmas` flags against the live registry.
pub fn all_names() -> Vec<&'static str> {
    all_descriptors().iter().map(|d| d.name).collect()
}
