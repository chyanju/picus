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
/// `var_names` is the producing builder's variable frame (used by
/// the SAT-side atom table to reverse-resolve `PolyTerm` indices to
/// names for `AtomKey` canonicalisation). `Sat(model)` carries the
/// FF variable assignments; `Unknown` is returned on cancellation,
/// theory `Unknown`, or iteration cap.
pub fn solve_formula(
    prime: BigUint,
    var_names: &[String],
    formula: &Formula,
    cancel: &CancelToken,
) -> SolveOutcome {
    let mut sat = Solver::new();
    let mut atoms = AtomTable::new(prime);
    let top = match tseitin(formula, var_names, &mut atoms, &mut sat) {
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
/// `Unknown`. Configured via [`crate::config::RuntimeConfig::cdclt_iter_cap`].
pub fn iter_cap() -> u64 {
    crate::config::with(|c| c.cdclt_iter_cap)
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
            // Snapshot trail length before `learn_clause` so the next
            // notify pass starts at the position the asserting literal
            // is about to occupy.
            let trail_pre_lemma = sat.trail_len();
            sat.learn_clause(learnt);
            if sat.should_restart() {
                sat.perform_restart();
            }
            sync_theory_after_backtrack(sat, theory, &mut theory_levels);
            notified = notified.min(trail_pre_lemma).min(sat.trail_len());
            continue;
        }

        sync_theory_after_propagate(sat, theory, &mut theory_levels);
        let trail = sat.trail();
        while notified < trail.len() {
            let lit = trail[notified];
            theory.notify_fact(lit.var(), lit.is_positive());
            notified += 1;
        }

        match run_theory_propagation(sat, theory) {
            TheoryStep::Progressed => continue,
            TheoryStep::Conflict(trail_pre_lemma) => {
                sync_theory_after_backtrack(sat, theory, &mut theory_levels);
                notified = notified.min(trail_pre_lemma).min(sat.trail_len());
                continue;
            }
            TheoryStep::RootUnsat => return SolveOutcome::Unsat(Vec::new()),
            TheoryStep::Idle => {}
        }

        if sat.all_assigned() {
            match theory.post_check(Effort::Full) {
                CheckOutcome::Sat => {
                    // The model returned by the theory's final
                    // `post_check(Full)` already covers every named
                    // variable: Bool vars are encoded as FF elements
                    // in {0, 1} in the polynomial namespace, so they
                    // come through the GB SAT point alongside the FF
                    // vars. SAT-only aux vars (Tseitin literals) are
                    // intentionally not surfaced.
                    let model = theory.collect_model().unwrap_or_default();
                    return SolveOutcome::Sat(model);
                }
                CheckOutcome::Unsat { core } => {
                    let trail_pre_lemma = apply_theory_conflict(sat, &core);
                    let trail_pre_lemma = match trail_pre_lemma {
                        Some(n) => n,
                        None => return SolveOutcome::Unsat(Vec::new()),
                    };
                    sync_theory_after_backtrack(sat, theory, &mut theory_levels);
                    notified = notified.min(trail_pre_lemma).min(sat.trail_len());
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

enum TheoryStep {
    /// No new derivation fired this round.
    Idle,
    /// At least one new literal was enqueued.
    Progressed,
    /// Lemma learnt and SAT backtracked; caller must sync theory.
    /// The wrapped value is the trail length right before the lemma's
    /// asserting literal was enqueued (see `add_theory_lemma_with_trail`).
    Conflict(usize),
    /// Lemma forced root-level UNSAT.
    RootUnsat,
}

/// One round of theory propagation. Each derived `(atom, polarity)`
/// becomes a no-op (SAT agrees), an `enqueue_theory` (SAT Undef), or a
/// theory lemma (SAT disagrees).
fn run_theory_propagation(sat: &mut Solver, theory: &mut FfTheory<'_>) -> TheoryStep {
    let props = theory.propagate();
    if props.is_empty() {
        return TheoryStep::Idle;
    }
    let mut progressed = false;
    for (atom_var, polarity) in props {
        let prop_lit = if polarity {
            Lit::pos(atom_var)
        } else {
            Lit::neg(atom_var)
        };
        match sat.value(atom_var) {
            LBool::Undef => {
                let reason_facts = theory.explain(atom_var, polarity);
                let reason_lits: Vec<Lit> = reason_facts
                    .iter()
                    .map(|&(v, p)| if p { Lit::pos(v) } else { Lit::neg(v) })
                    .collect();
                if sat.enqueue_theory(prop_lit, reason_lits) {
                    progressed = true;
                }
            }
            LBool::True if polarity => {}
            LBool::False if !polarity => {}
            _ => {
                let reason_facts = theory.explain(atom_var, polarity);
                let mut lemma: Vec<Lit> = Vec::with_capacity(reason_facts.len() + 1);
                lemma.push(prop_lit);
                for (fav, fpol) in reason_facts {
                    let fl = if fpol { Lit::pos(fav) } else { Lit::neg(fav) };
                    lemma.push(-fl);
                }
                match sat.add_theory_lemma_with_trail(lemma) {
                    Some(trail_pre) => return TheoryStep::Conflict(trail_pre),
                    None => return TheoryStep::RootUnsat,
                }
            }
        }
    }
    if progressed {
        TheoryStep::Progressed
    } else {
        TheoryStep::Idle
    }
}

/// Turn an atom-core into a SAT lemma and apply it. On success returns
/// `Some(trail_len_before_asserting)` (the position the lemma's
/// asserting literal sits at after the internal backtrack). Returns
/// `None` if the lemma forces root-level UNSAT. An Undef core var
/// indicates the theory's push/pop state diverged from SAT's.
fn apply_theory_conflict(sat: &mut Solver, core: &[Var]) -> Option<usize> {
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
    sat.add_theory_lemma_with_trail(lits)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean::{Formula, Literal};
    use crate::encoder::PolyTerm;
    use num_bigint::BigUint;

    /// `coeff * <var idx> = rhs_const`.
    fn eq(coeff_lhs: u64, var_idx: u32, rhs_const: u64) -> Formula {
        Formula::Lit(Literal::Eq(
            vec![PolyTerm {
                coeff: BigUint::from(coeff_lhs),
                vars: vec![(var_idx, 1)],
            }],
            vec![PolyTerm {
                coeff: BigUint::from(rhs_const),
                vars: vec![],
            }],
        ))
    }

    fn names(ns: &[&str]) -> Vec<String> {
        ns.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn solve_trivial_eq() {
        let vn = names(&["x"]);
        let f = eq(1, 0, 5);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        match r {
            SolveOutcome::Sat(m) => {
                assert_eq!(m.get("x"), Some(&BigUint::from(5u32)));
            }
            other => panic!("expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn solve_contradictory_eqs() {
        let vn = names(&["x"]);
        let f = Formula::And(vec![eq(1, 0, 5), eq(1, 0, 6)]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_or_picks_satisfiable_branch() {
        let vn = names(&["x"]);
        let f = Formula::Or(vec![eq(1, 0, 5), eq(1, 0, 6)]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
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
        let vn = names(&["x"]);
        let f = Formula::And(vec![
            Formula::Or(vec![eq(1, 0, 0), eq(1, 0, 1)]),
            eq(1, 0, 7),
        ]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_eq_and_neq() {
        let vn = names(&["x"]);
        let f = Formula::And(vec![eq(1, 0, 5), Formula::Not(Box::new(eq(1, 0, 5)))]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn solve_implies_chain() {
        let vn = names(&["x", "y"]);
        let f = Formula::And(vec![
            eq(1, 0, 0),
            Formula::Or(vec![Formula::Not(Box::new(eq(1, 0, 0))), eq(1, 1, 0)]),
            Formula::Not(Box::new(eq(1, 1, 0))),
        ]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn iter_cap_returns_unknown_on_pathological_input() {
        let _g = crate::config::ConfigGuard::with_override(|c| c.cdclt_iter_cap = 0);
        let vn = names(&["x"]);
        let f = Formula::Or(vec![eq(1, 0, 5), eq(1, 0, 6)]);
        let r = solve_formula(BigUint::from(101u32), &vn, &f, &CancelToken::none());
        assert!(matches!(r, SolveOutcome::Unknown));
    }
}
