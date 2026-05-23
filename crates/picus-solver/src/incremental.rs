//! Incremental solver: push / pop / check API.
//!
//! A simple push/pop interface backed by a stack of checkpoint heights
//! into a single `Vec<Constraint>`. Each `check()` rebuilds a fresh
//! [`ConstraintSystemBuilder`] from the accumulated facts and
//! dispatches to [`crate::core::solve_encoded_with_cancel`].
//!
//! Facts are stored in name-keyed form ([`NamedTerm`]) because the
//! push/pop API can't fix variable indices until check time — each
//! check builds a fresh polynomial ring with its own index frame.

use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::core::{solve_encoded_with_cancel, SolveOutcome};
use crate::encoder::{encode, ConstraintSystemBuilder, PolyTerm, VarIdx};
use crate::timeout::CancelToken;

/// AST scratch term: `coeff * prod(vars)` with `vars` carrying
/// repeated names for higher exponents (`vec!["x", "x"]` = `x^2`).
/// Used by [`IncrementalSolver::assert_equality`] for incremental
/// fact storage; converted to [`PolyTerm`] at check time.
#[derive(Clone, Debug)]
pub struct NamedTerm {
    pub coeff: BigUint,
    pub vars: Vec<String>,
}

/// A single constraint that can be asserted incrementally.
#[derive(Clone, Debug)]
pub enum Constraint {
    /// A polynomial equation: sum(terms) == 0.
    Equality(Vec<NamedTerm>),
    /// A disequality: var_a != var_b.
    Disequality(String, String),
    /// A direct variable assignment: var == value.
    Assignment(String, BigUint),
}

/// Incremental solver state.
pub struct IncrementalSolver {
    prime: BigUint,
    add_field_polys: bool,
    facts: Vec<Constraint>,
    /// Stack of `facts.len()` snapshots taken at each `push`.
    push_stack: Vec<usize>,
}

impl IncrementalSolver {
    /// Create a new incremental solver over `GF(prime)`.  If
    /// `add_field_polys` is true, field polynomials `x^p - x` are added
    /// for each variable on every check (typically only needed for very
    /// small primes).
    pub fn new(prime: BigUint, add_field_polys: bool) -> Self {
        IncrementalSolver {
            prime,
            add_field_polys,
            facts: Vec::new(),
            push_stack: Vec::new(),
        }
    }

    /// Save a checkpoint.  Subsequent `pop` returns to this state.
    pub fn push(&mut self) {
        self.push_stack.push(self.facts.len());
    }

    /// Discard all facts added since the most recent `push`.
    /// No-op if no checkpoint exists.
    pub fn pop(&mut self) {
        if let Some(height) = self.push_stack.pop() {
            self.facts.truncate(height);
        }
    }

    /// Number of pending push checkpoints.
    pub fn push_depth(&self) -> usize { self.push_stack.len() }

    /// Number of asserted facts at the current level.
    pub fn num_facts(&self) -> usize { self.facts.len() }

    /// Assert a polynomial equation `sum(terms) == 0`.
    pub fn assert_equality(&mut self, terms: Vec<NamedTerm>) {
        self.facts.push(Constraint::Equality(terms));
    }

    /// Assert `a != b`.
    pub fn assert_disequality(&mut self, a: impl Into<String>, b: impl Into<String>) {
        self.facts.push(Constraint::Disequality(a.into(), b.into()));
    }

    /// Assert `var = value`.
    pub fn assert_assignment(&mut self, var: impl Into<String>, value: BigUint) {
        self.facts.push(Constraint::Assignment(var.into(), value));
    }

    /// Solve the current fact set. Encodes from scratch and dispatches to
    /// the Split GB engine.
    pub fn check(&self) -> SolveOutcome {
        self.check_with_cancel(&CancelToken::none())
    }

    /// Solve the current fact set with cooperative cancellation.
    pub fn check_with_cancel(&self, cancel: &CancelToken) -> SolveOutcome {
        let mut builder = ConstraintSystemBuilder::new(self.prime.clone());
        builder.set_add_field_polys(self.add_field_polys);
        for fact in &self.facts {
            match fact {
                Constraint::Equality(terms) => {
                    let intern_terms: Vec<PolyTerm> = terms
                        .iter()
                        .map(|t| {
                            let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
                            for v in &t.vars {
                                let idx = builder.var(v);
                                *counts.entry(idx).or_insert(0) += 1;
                            }
                            PolyTerm {
                                coeff: t.coeff.clone(),
                                vars: counts.into_iter().collect(),
                            }
                        })
                        .collect();
                    builder.add_equality(intern_terms);
                }
                Constraint::Disequality(a, b) => {
                    let ai = builder.var(a);
                    let bi = builder.var(b);
                    builder.add_disequality(ai, bi);
                }
                Constraint::Assignment(v, val) => {
                    let vi = builder.var(v);
                    builder.add_assignment(vi, val.clone());
                }
            }
        }
        let sys = builder.build();
        let encoded = match encode(&sys) {
            Ok(e) => e,
            Err(e) => {
                log::error!("encode failed: {e}");
                return SolveOutcome::Unknown;
            }
        };
        solve_encoded_with_cancel(&encoded, cancel)
    }

    /// Solve with a timeout duration.
    pub fn check_with_timeout(&self, timeout: std::time::Duration) -> SolveOutcome {
        let cancel = CancelToken::with_timeout(timeout);
        self.check_with_cancel(&cancel)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(coeff: u32, vars: &[&str]) -> NamedTerm {
        NamedTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn test_push_pop_basic() {
        let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
        solver.assert_assignment("x", BigUint::from(2u32));
        match solver.check() {
            SolveOutcome::Sat(_) => {}
            _ => panic!("expected SAT before push"),
        }
        solver.push();
        solver.assert_assignment("x", BigUint::from(3u32));
        match solver.check() {
            SolveOutcome::Unsat(_) => {}
            _ => panic!("expected UNSAT after adding contradiction"),
        }
        solver.pop();
        match solver.check() {
            SolveOutcome::Sat(m) => assert_eq!(m["x"], BigUint::from(2u32)),
            _ => panic!("expected SAT after pop"),
        }
    }

    #[test]
    fn test_nested_push_pop() {
        let mut solver = IncrementalSolver::new(BigUint::from(11u32), false);
        // x + y - 7 = 0
        solver.assert_equality(vec![
            term(1, &["x"]),
            term(1, &["y"]),
            NamedTerm { coeff: BigUint::from(11u32 - 7), vars: vec![] },
        ]);
        solver.push();
        solver.assert_assignment("x", BigUint::from(3u32));
        solver.push();
        solver.assert_assignment("y", BigUint::from(4u32));
        match solver.check() {
            SolveOutcome::Sat(m) => {
                assert_eq!(m["x"], BigUint::from(3u32));
                assert_eq!(m["y"], BigUint::from(4u32));
            }
            _ => panic!("expected SAT at depth 2"),
        }
        solver.pop();
        solver.assert_assignment("y", BigUint::from(5u32));
        match solver.check() {
            SolveOutcome::Unsat(_) => {}
            _ => panic!("expected UNSAT at depth 2 with y=5"),
        }
        solver.pop();
        assert_eq!(solver.push_depth(), 0);
        match solver.check() {
            SolveOutcome::Sat(_) => {}
            _ => panic!("expected SAT at depth 0"),
        }
    }
}
