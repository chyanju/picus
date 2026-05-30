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
}

impl<T: Theory> EeFilteredTheory<T> {
    pub fn new(ee: EqualityEngine, inner: T) -> Self {
        Self { ee, inner }
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
                // Still forward: the canonical-polynomial union already
                // told us this fact would conflict with a prior trail
                // entry, but without a precise lemma synthesis path the
                // sound thing is to let the inner theory's GB collapse
                // detect UNSAT at `post_check`. A future round can
                // shortcut via a 2-literal theory lemma.
                self.inner.notify_fact(atom, polarity);
            }
        }
    }

    fn post_check(&mut self) -> CheckOutcome {
        self.inner.post_check()
    }

    fn propagate(&mut self) -> Vec<(Var, bool)> {
        self.inner.propagate()
    }

    fn explain(&self, atom: Var, polarity: bool) -> Vec<(Var, bool)> {
        self.inner.explain(atom, polarity)
    }

    fn push(&mut self) {
        self.ee.push();
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
        self.ee.pop();
    }

    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        self.inner.collect_model()
    }
}

#[cfg(test)]
#[path = "ee_filtered_tests.rs"]
mod tests;
