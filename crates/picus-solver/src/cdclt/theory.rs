//! Theory plug-in interface for CDCL(T).
//!
//! Shape matches cvc5's `Theory` virtual class:
//! the SAT engine calls [`Theory::notify_fact`] on every committed literal
//! and [`Theory::post_check`] at a candidate full assignment. The theory
//! returns `Sat` / `Unsat(core)` / `Unknown`; the orchestrator turns the
//! core into a SAT lemma.
//!
//! [`propagate`] defaults to no propagation and [`explain`] to a panic;
//! the FF theory overrides both.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::sat::Var;

/// Outcome of a theory check.
#[derive(Debug)]
pub enum CheckOutcome {
    /// All asserted facts are consistent.
    Sat,
    /// A subset of asserted-True atom vars is inconsistent. The
    /// orchestrator will learn `(¬v_1 ∨ … ∨ ¬v_k)` as a SAT clause.
    /// For atom vars that were asserted False at the time of the
    /// theory call, the orchestrator will include their negations
    /// (i.e. the positive literal) in the learnt clause via its
    /// trail bookkeeping.
    Unsat {
        /// Atom variables that the theory identifies as participating
        /// in the conflict.
        core: Vec<Var>,
    },
    /// Theory could not decide (e.g. timeout, incompleteness).
    Unknown,
}

/// Theory plug-in interface.
pub trait Theory {
    /// SAT just committed `(atom, polarity)`. Theory should record
    /// this so a later `post_check` can reason about it. Order
    /// matters: facts arrive in SAT trail order.
    fn notify_fact(&mut self, atom: Var, polarity: bool);

    /// Required check, called when SAT has a candidate model. The FF
    /// theory's GB invocation lives here.
    fn post_check(&mut self) -> CheckOutcome;

    /// Theory propagation: atoms the theory derives must be True or
    /// False given the current facts. Each entry is `(atom_var,
    /// polarity)`. Default: no propagation.
    fn propagate(&mut self) -> Vec<(Var, bool)> {
        Vec::new()
    }

    /// Justification for a propagated literal. Required only if
    /// `propagate` ever returns non-empty.
    fn explain(&self, _atom: Var, _polarity: bool) -> Vec<(Var, bool)> {
        unreachable!("theory does not propagate; explain must not be called")
    }

    /// SAT entered a new decision level. Theory may want to snapshot
    /// state. Default: noop.
    fn push(&mut self) {}

    /// SAT backtracked to an earlier decision level. Theory must
    /// roll its state back symmetrically. Default: noop.
    fn pop(&mut self) {}

    /// On a `Sat` outcome, return the FF variable assignments that
    /// realize the model. Used by the orchestrator to compose the
    /// final SMT model. Default: empty.
    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        None
    }
}
