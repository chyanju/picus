//! CDCL(T) main loop.
//!
//! Drives [`sat::Solver`] step by step, notifying the theory plug-in
//! of each newly-committed literal and consulting it at full
//! assignment. Theory conflicts become learnt clauses via
//! [`sat::Solver::add_theory_lemma`].

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::boolean::Formula;
use crate::core::SolveOutcome;
use crate::sat::{LBool, Lit, Solver, Var};
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::cnf::{tseitin, TseitinResult};
use super::ff_theory::FfTheory;
use super::theory::{CheckOutcome, Effort, Theory};

/// Solve a `Formula` over GF(`prime`) via CDCL(T) with the FF theory.
/// `Sat(model)` carries the FF variable assignments; `Unknown` is
/// returned on cancellation, theory `Unknown`, or iteration cap.
pub fn solve_formula(
    prime: BigUint,
    formula: &Formula,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut sat = Solver::new();
    let mut atoms = AtomTable::new(prime);
    let top = match tseitin(formula, &mut atoms, &mut sat) {
        TseitinResult::Constant(true) => return SolveOutcome::Sat(HashMap::new()),
        TseitinResult::Constant(false) => return SolveOutcome::Unsat(Vec::new()),
        TseitinResult::Lit(l) => l,
    };
    if !sat.add_clause(vec![top]) {
        return SolveOutcome::Unsat(Vec::new());
    }
    if sat.is_unsat() {
        return SolveOutcome::Unsat(Vec::new());
    }

    let mut theory = FfTheory::new(&atoms, cancel);
    cdclt_loop(&mut sat, &mut theory, cancel)
}

/// Max CDCL(T) main-loop iterations before [`cdclt_loop`] returns
/// `Unknown`. Override via `PICUS_CDCLT_ITER_CAP` (default `1_000_000`).
pub fn iter_cap() -> u64 {
    std::env::var("PICUS_CDCLT_ITER_CAP")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(1_000_000)
}

fn cdclt_loop(
    sat: &mut Solver,
    theory: &mut FfTheory<'_>,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut notified: usize = 0;
    let mut theory_levels: usize = 0;
    let cap = iter_cap();
    let mut iters: u64 = 0;

    loop {
        if cancel.is_cancelled() {
            return SolveOutcome::Unknown;
        }
        iters += 1;
        if iters > cap {
            return SolveOutcome::Unknown;
        }

        if let Some(conflict) = sat.propagate() {
            if sat.decision_level() == 0 {
                return SolveOutcome::Unsat(Vec::new());
            }
            let (learnt, bt) = sat.analyze(conflict);
            sat.backtrack_to(bt);
            sat.learn_clause(learnt);
            if sat.should_restart() {
                sat.perform_restart();
            }
            sync_theory_after_backtrack(sat, theory, &mut theory_levels);
            notified = notified.min(sat.trail_len());
            continue;
        }

        sync_theory_after_propagate(sat, theory, &mut theory_levels);
        let trail = sat.trail();
        while notified < trail.len() {
            let lit = trail[notified];
            theory.notify_fact(lit.var(), lit.is_positive());
            notified += 1;
        }

        if sat.all_assigned() {
            match theory.post_check(Effort::Full) {
                CheckOutcome::Sat => {
                    let mut model = build_full_model(sat, theory);
                    if let Some(theory_model) = theory.collect_model() {
                        for (k, v) in theory_model {
                            model.insert(k, v);
                        }
                    }
                    return SolveOutcome::Sat(model);
                }
                CheckOutcome::Unsat { core } => {
                    if !apply_theory_conflict(sat, &core) {
                        return SolveOutcome::Unsat(Vec::new());
                    }
                    sync_theory_after_backtrack(sat, theory, &mut theory_levels);
                    notified = notified.min(sat.trail_len());
                    continue;
                }
                CheckOutcome::Unknown => return SolveOutcome::Unknown,
            }
        }

        // Step 4: Decide.
        let next = sat.pick_decision().expect("not all assigned ⇒ Undef var exists");
        let ok = sat.decide(next);
        debug_assert!(ok);
    }
}

/// Turn an atom-core into a SAT lemma (negation of each atom's current
/// value) and feed it via [`Solver::add_theory_lemma`]. Returns `false`
/// when the lemma forces root-level UNSAT. Core variables must be
/// assigned; an Undef core var indicates the theory's push/pop state
/// diverged from SAT's and is treated as an invariant violation.
fn apply_theory_conflict(sat: &mut Solver, core: &[Var]) -> bool {
    let mut lits: Vec<Lit> = Vec::with_capacity(core.len());
    for &v in core {
        match sat.value(v) {
            LBool::True => lits.push(Lit::neg(v)),
            LBool::False => lits.push(Lit::pos(v)),
            LBool::Undef => unreachable!(
                "theory core var {:?} is Undef: theory/SAT push/pop diverged",
                v
            ),
        }
    }
    sat.add_theory_lemma(lits)
}

fn sync_theory_after_propagate(
    sat: &Solver,
    theory: &mut FfTheory<'_>,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    while *theory_levels < dl {
        theory.push();
        *theory_levels += 1;
    }
}

fn sync_theory_after_backtrack(
    sat: &Solver,
    theory: &mut FfTheory<'_>,
    theory_levels: &mut usize,
) {
    let dl = sat.decision_level() as usize;
    while *theory_levels > dl {
        theory.pop();
        *theory_levels -= 1;
    }
}

fn build_full_model(_sat: &Solver, _theory: &FfTheory<'_>) -> HashMap<String, BigUint> {
    HashMap::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean::{Formula, Literal};
    use crate::encoder::PolyTerm;
    use num_bigint::BigUint;

    fn t(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn eq(coeff_lhs: u64, var: &str, rhs_const: u64) -> Formula {
        Formula::Lit(Literal::Eq(
            vec![t(coeff_lhs, &[var])],
            vec![t(rhs_const, &[])],
        ))
    }

    #[test]
    fn solve_trivial_eq() {
        // (= x 5): SAT.
        let f = eq(1, "x", 5);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                assert_eq!(m.get("x"), Some(&BigUint::from(5u32)));
            }
            other => panic!("expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn solve_contradictory_eqs() {
        // (and (= x 5) (= x 6)): UNSAT.
        let f = Formula::And(vec![eq(1, "x", 5), eq(1, "x", 6)]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_or_picks_satisfiable_branch() {
        // (or (= x 5) (= x 6)): both branches independently SAT.
        let f = Formula::Or(vec![eq(1, "x", 5), eq(1, "x", 6)]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                let v = m.get("x").expect("x assigned").clone();
                assert!(v == BigUint::from(5u32) || v == BigUint::from(6u32));
            }
            other => panic!("expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn solve_disjunctive_bit_via_cdclt() {
        // (or (= x 0) (= x 1)) ∧ (= x 7): UNSAT (x can't be 7 and 0/1).
        let f = Formula::And(vec![
            Formula::Or(vec![eq(1, "x", 0), eq(1, "x", 1)]),
            eq(1, "x", 7),
        ]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_eq_and_neq() {
        // (and (= x 5) (not (= x 5))): UNSAT.
        let f = Formula::And(vec![
            eq(1, "x", 5),
            Formula::Not(Box::new(eq(1, "x", 5))),
        ]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_implies_chain() {
        // (and (= x 0) (=> (= x 0) (= y 0)) (not (= y 0))): UNSAT.
        let f = Formula::And(vec![
            eq(1, "x", 0),
            // (=> (= x 0) (= y 0)) ≡ (or (not (= x 0)) (= y 0))
            Formula::Or(vec![
                Formula::Not(Box::new(eq(1, "x", 0))),
                eq(1, "y", 0),
            ]),
            Formula::Not(Box::new(eq(1, "y", 0))),
        ]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn iter_cap_returns_unknown_on_pathological_input() {
        // Cap = 0 forces an immediate Unknown bail-out. ENV_TEST_LOCK
        // serializes against the boolean.rs DNF-cap test.
        let _env_lock = crate::ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        struct EnvGuard(&'static str);
        impl Drop for EnvGuard {
            fn drop(&mut self) {
                unsafe { std::env::remove_var(self.0); }
            }
        }
        unsafe { std::env::set_var("PICUS_CDCLT_ITER_CAP", "0"); }
        let _g = EnvGuard("PICUS_CDCLT_ITER_CAP");
        let f = Formula::Or(vec![eq(1, "x", 5), eq(1, "x", 6)]);
        let r = solve_formula(BigUint::from(101u32), &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unknown));
    }
}
