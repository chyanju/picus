use super::*;
use crate::boolean::{Formula, Literal};
use crate::frontend::encoder::PolyTerm;
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

#[test]
fn theory_core_undef_var_gives_up_not_panic() {
    // A theory UNSAT core that names a SAT-unassigned variable signals
    // theory/SAT trail divergence. `apply_theory_conflict` must flag
    // give-up (so the loop returns Unknown), never panic or fabricate a
    // verdict from a partial core.
    let mut sat = Solver::new();
    let v = sat.new_var(); // freshly created ⇒ unassigned (Undef)
    assert!(matches!(sat.value(v), LBool::Undef));
    let result = apply_theory_conflict(&mut sat, &[v]);
    assert!(result.is_none(), "a diverged core must not produce a lemma");
    assert!(
        sat.gave_up(),
        "must flag give-up so the caller returns Unknown"
    );
}
