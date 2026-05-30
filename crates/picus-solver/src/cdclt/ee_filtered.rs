//! Equality-engine fact filter wrapping an inner [`Theory`].
//!
//! Implements [`Theory`] over a paired `(EqualityEngine, T)` so the
//! orchestrator can interpose canonical-polynomial atom dedup before the
//! underlying FF theory sees a fact. `Fresh` outcomes forward to the
//! inner theory; `Redundant` outcomes are dropped (the same canonical
//! polynomial at the same polarity is already on the trail); `Contradiction`
//! outcomes are forwarded too — the inner theory's GB layer will detect
//! the conflict at `post_check`, so the EE-side polarity contradiction is
//! a hint, not the primary signal, until a precise lemma synthesis is
//! added in a later round.
//!
//! `push` / `pop` run in lockstep: EE first on push, inner first on pop,
//! mirroring the SAT-trail invariant — a polarity asserted at level k
//! must be visible to both engines through all of k..=current_dl.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::sat::Var;

use super::equality_engine::{EqualityEngine, NotifyOutcome};
use super::theory::{CheckOutcome, Theory};

pub struct EeFilteredTheory<T: Theory> {
    ee: EqualityEngine,
    inner: T,
    /// Set by `notify_fact` when the EE detects a polarity contradiction
    /// at notify time. The pair is `(new_atom, prior_witness_atom)` —
    /// the 2-literal lemma `{¬lit(new, polarity), ¬lit(witness,
    /// !polarity)}` synthesises directly from this without consulting
    /// the inner theory's GB layer. Consumed by `post_check` and
    /// cleared on `pop` if the level that produced it is undone before
    /// the consumer fires.
    pending_contradiction: Option<(Var, bool, Var, bool)>,
    /// `pending_contradiction` snapshot per level for symmetric rollback
    /// on `pop`. Length must equal `theory_levels` after every matched
    /// push/pop pair.
    pending_levels: Vec<Option<(Var, bool, Var, bool)>>,
}

impl<T: Theory> EeFilteredTheory<T> {
    pub fn new(ee: EqualityEngine, inner: T) -> Self {
        Self {
            ee,
            inner,
            pending_contradiction: None,
            pending_levels: Vec::new(),
        }
    }

    pub fn inner(&self) -> &T {
        &self.inner
    }

    pub fn inner_mut(&mut self) -> &mut T {
        &mut self.inner
    }

    pub fn ee(&self) -> &EqualityEngine {
        &self.ee
    }
}

impl<T: Theory> Theory for EeFilteredTheory<T> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        match self.ee.notify(atom, polarity) {
            NotifyOutcome::Fresh => self.inner.notify_fact(atom, polarity),
            NotifyOutcome::Redundant => {}
            NotifyOutcome::Contradiction => {
                // Synthesize the 2-lit contradiction: `atom` at
                // `polarity` plus the prior witness at `!polarity` are
                // both asserted; the inner theory's GB layer would also
                // detect UNSAT at post_check from these two literals,
                // but the EE knows the precise pair already so we
                // short-circuit. Still forward to keep the inner
                // theory's trail in sync (some inner impls inspect the
                // trail at push/pop or rebuild on resync).
                let rep = self.ee.rep_of(atom);
                if let Some(witness) = self.ee.prior_witness(rep) {
                    if witness != atom {
                        self.pending_contradiction =
                            Some((atom, polarity, witness, !polarity));
                    }
                }
                self.inner.notify_fact(atom, polarity);
            }
        }
    }

    fn post_check(&mut self) -> CheckOutcome {
        if let Some((atom, _, witness, _)) = self.pending_contradiction.take() {
            return CheckOutcome::Unsat {
                core: vec![atom, witness],
            };
        }
        self.inner.post_check()
    }

    fn propagate(&mut self) -> Vec<(Var, bool)> {
        self.inner.propagate()
    }

    fn explain(&self, atom: Var, polarity: bool) -> Vec<(Var, bool)> {
        self.inner.explain(atom, polarity)
    }

    fn push(&mut self) {
        self.pending_levels.push(self.pending_contradiction);
        self.ee.push();
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
        self.ee.pop();
        if let Some(prev) = self.pending_levels.pop() {
            // The level that produced any pending contradiction is being
            // undone; restore the snapshot from before the push.
            self.pending_contradiction = prev;
        } else {
            // Unbalanced pop — clear defensively so a stale pending
            // cannot leak across solve boundaries.
            self.pending_contradiction = None;
        }
    }

    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        self.inner.collect_model()
    }
}

#[cfg(test)]
#[path = "ee_filtered_tests.rs"]
mod tests;
