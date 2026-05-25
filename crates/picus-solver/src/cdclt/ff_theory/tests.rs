use super::*;
use std::collections::BTreeMap;

use crate::cdclt::atoms::{AtomTable, InternResult};
use crate::encoder::PolyTerm;
use crate::sat::Solver;
use num_bigint::BigUint;

/// Interns `name` into `vn` (returning a stable `u32` index) and
/// reuses the existing slot for repeat calls.
fn ensure_var(vn: &mut Vec<String>, name: &str) -> u32 {
    if let Some(i) = vn.iter().position(|n| n == name) {
        return i as u32;
    }
    vn.push(name.to_string());
    (vn.len() - 1) as u32
}

/// `coeff * prod(vars)` as a `PolyTerm`, collapsing repeated name
/// occurrences into `(VarIdx, exp)` pairs.
fn t(vn: &mut Vec<String>, coeff: u64, vars: &[&str]) -> PolyTerm {
    let mut counts: BTreeMap<u32, u16> = BTreeMap::new();
    for n in vars {
        let idx = ensure_var(vn, n);
        *counts.entry(idx).or_insert(0) += 1;
    }
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: counts.into_iter().collect(),
    }
}

/// Atom variable for `(= var const)` over the given table + SAT.
fn intern_eq_var(
    tbl: &mut AtomTable,
    sat: &mut Solver,
    vn: &mut Vec<String>,
    var: &str,
    c: u64,
) -> Var {
    let lhs = vec![t(vn, 1, &[var])];
    let rhs = vec![t(vn, c, &[])];
    let r = tbl.intern_eq(&lhs, &rhs, vn, sat);
    match r {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    }
}

/// Atom variable for arbitrary `(= sum_lhs sum_rhs)` from
/// `&[(coeff, &[var_names])]` term specs.
fn intern_eq_terms(
    tbl: &mut AtomTable,
    sat: &mut Solver,
    vn: &mut Vec<String>,
    lhs_spec: &[(u64, &[&str])],
    rhs_spec: &[(u64, &[&str])],
) -> Var {
    let lhs: Vec<PolyTerm> = lhs_spec.iter().map(|(c, vs)| t(vn, *c, vs)).collect();
    let rhs: Vec<PolyTerm> = rhs_spec.iter().map(|(c, vs)| t(vn, *c, vs)).collect();
    match tbl.intern_eq(&lhs, &rhs, vn, sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    }
}

#[test]
fn empty_trail_is_sat() {
    let prime = BigUint::from(101u32);
    let atoms = AtomTable::new(prime);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    match th.post_check(Effort::Full) {
        CheckOutcome::Sat => {}
        other => panic!("expected Sat, got {:?}", other),
    }
}

#[test]
fn single_eq_sat() {
    // (= x 5): SAT, model x=5.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let av = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(av, true);
    match th.post_check(Effort::Full) {
        CheckOutcome::Sat => {}
        other => panic!("expected Sat, got {:?}", other),
    }
    let m = th.collect_model().expect("model present");
    assert_eq!(m.get("x"), Some(&BigUint::from(5u32)));
}

#[test]
fn two_contradictory_eqs_unsat() {
    // (= x 5) ∧ (= x 6): UNSAT, core includes both atoms.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a1 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let a2 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a1, true);
    th.notify_fact(a2, true);
    match th.post_check(Effort::Full) {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&a1));
            assert!(core.contains(&a2));
        }
        other => panic!("expected Unsat, got {:?}", other),
    }
}

#[test]
fn neq_via_negative_polarity() {
    // (= x 5) ∧ (¬(= x 5)): the same atom asserted with both
    // polarities — SAT layer would catch this, but the theory
    // also handles it via the Rabinowitsch encoding.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let av = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(av, true);
    th.notify_fact(av, false);
    match th.post_check(Effort::Full) {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&av));
        }
        other => panic!("expected Unsat, got {:?}", other),
    }
}

#[test]
fn push_pop_undoes_facts() {
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let av = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.push();
    th.notify_fact(av, true);
    assert_eq!(th.facts.len(), 1);
    th.pop();
    assert_eq!(th.facts.len(), 0);
}

#[test]
fn propagate_empty_when_no_pinned_vars() {
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let _ = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    // Without any True fact, no var is pinned ⇒ no propagation.
    assert!(th.propagate().is_empty());
}

#[test]
fn propagate_pins_force_other_atom_truth() {
    // Two atoms over the same variable: (= x 5) and (= x 6).
    // Asserting (= x 5) True pins x = 5; propagation then derives
    // (= x 6) is False.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let a6 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a5, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == a6 && !p),
        "expected (a6, false) in propagations: {:?}",
        props
    );
}

#[test]
fn propagate_pins_force_multi_var_atom_true() {
    // (= (ff.add x y) 7) with x=3, y=4 evaluates to 0 ⇒ atom True.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax, true);
    th.notify_fact(ay, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == asum && p),
        "expected (asum, true): {:?}",
        props
    );
}

#[test]
fn explain_returns_only_relevant_pinning_facts() {
    // Pin x=3 and y=4; the propagated atom (x+y=7) depends on both,
    // so explain must return both. A third pinned variable z that
    // doesn't appear in the atom must NOT show up.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
    let az = intern_eq_var(&mut atoms, &mut sat, &mut vn, "z", 9);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax, true);
    th.notify_fact(ay, true);
    th.notify_fact(az, true);
    let _ = th.propagate(); // populate pending_reasons
    let reason = th.explain(asum, true);
    let reason_vars: std::collections::HashSet<Var> = reason.iter().map(|&(v, _)| v).collect();
    assert!(reason_vars.contains(&ax));
    assert!(reason_vars.contains(&ay));
    assert!(!reason_vars.contains(&az), "z should not appear in reason");
}

#[test]
fn propagate_ignores_negative_polarity_facts() {
    // (≠) facts must not contribute to pinning.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let _a6 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a5, false);
    assert!(
        th.propagate().is_empty(),
        "negative-polarity (x ≠ 5) must not pin x to 5"
    );
}

#[test]
fn propagate_ignores_auxiliary_variables() {
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let _a5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let aux = atoms.new_aux(&mut sat);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(aux, true);
    assert_eq!(th.facts.len(), 0, "aux var must not be recorded");
    assert!(th.propagate().is_empty());
}

#[test]
fn propagate_handles_degree_two_atom_when_var_pinned() {
    // x=2 + (x*x = 4) atom ⇒ True under substitution.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax2 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 2);
    let asq = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x", "x"])],
        &[(4, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax2, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == asq && p),
        "(x*x = 4) under x=2 must propagate True: {:?}",
        props
    );
}

#[test]
fn propagate_skips_atom_with_unpinned_variable() {
    // Tier 1 requires all vars pinned; partial pinning must skip.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    let props = th.propagate();
    assert!(
        !props.iter().any(|&(v, _)| v == asum),
        "(x+y=7) must not propagate while y is unpinned: {:?}",
        props
    );
}

#[test]
fn pinning_is_idempotent_across_canonically_distinct_but_equivalent_atoms() {
    // (= x 5) and (2x = 10) both pin x=5 via Fermat.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a_x5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let a_2x10 = intern_eq_terms(&mut atoms, &mut sat, &mut vn, &[(2, &["x"])], &[(10, &[])]);
    let a_x6 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a_x5, true);
    th.notify_fact(a_2x10, true);
    let pinned = th.pinned_vars();
    let (value, _src) = pinned.get("x").expect("x must be pinned");
    assert_eq!(value, &BigUint::from(5u32));
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == a_x6 && !p),
        "x=5 (asserted twice canonically distinct) must still derive x≠6: {:?}",
        props
    );
}

#[test]
fn propagate_handles_constant_only_atoms_without_panic() {
    // (= 0 1) interns as a vars-empty atom; propagate must not panic.
    let prime = BigUint::from(7u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let av = intern_eq_terms(&mut atoms, &mut sat, &mut vn, &[(0, &[])], &[(1, &[])]);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(av, true);
    let _ = th.propagate(); // must not panic
}

#[test]
fn tier2_linear_residue_derives_target_atom_true() {
    // x=3 + (x+y=7) ⇒ y=4 ⇒ (= y 4) True.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == ay4 && p),
        "Tier 2 must derive (= y 4) True from (= x 3) and (= (x+y) 7): {:?}",
        props
    );
}

#[test]
fn tier2_propagates_false_for_non_matching_value_atom() {
    // Derived y=4 ⇒ (= y 5) False.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let _ay4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
    let ay5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 5);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == ay5 && !p),
        "Tier 2 must derive (= y 5) False (derived value is 4): {:?}",
        props
    );
}

#[test]
fn tier2_skips_multiple_unpinned_variables() {
    // (x+y+z=10) with only x pinned: 2 unpinned vars ⇒ Tier 2 bails.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let _ay7 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 7);
    let _az0 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "z", 0);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"]), (1, &["z"])],
        &[(10, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let props = th.propagate();
    for (av, _) in &props {
        assert_ne!(*av, _ay7);
        assert_ne!(*av, _az0);
    }
}

#[test]
fn tier2_skips_degree_two_in_unpinned() {
    // (y*z = 12) has a bivariate unpinned term ⇒ Tier 2 bails.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let _ay3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 3);
    let aprod = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["y", "z"])],
        &[(12, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(aprod, true);
    let props = th.propagate();
    assert!(!props.iter().any(|&(v, _)| v == aprod));
}

#[test]
fn tier2_explain_includes_source_atom_and_other_pinning_facts() {
    // Reason for (= y 4) True = {source (x+y=7), pinning (= x 3)}.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(7, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let _ = th.propagate();
    let reason = th.explain(ay4, true);
    let reason_vars: std::collections::HashSet<Var> = reason.iter().map(|&(v, _)| v).collect();
    assert!(
        reason_vars.contains(&asum),
        "Tier 2 reason must cite the source atom: {:?}",
        reason
    );
    assert!(
        reason_vars.contains(&ax3),
        "Tier 2 reason must cite the pinning fact: {:?}",
        reason
    );
}

#[test]
fn tier2_nonlinear_coefficient_from_pinned_factor() {
    // (x*y = 12) with x=4 pinned: 4y=12 ⇒ y=3.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);
    let ay3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 3);
    let aprod = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x", "y"])],
        &[(12, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax4, true);
    th.notify_fact(aprod, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == ay3 && p),
        "Tier 2 with non-unit pinned-factor coefficient must solve 4y=12 ⇒ y=3: {:?}",
        props
    );
}

#[test]
fn pop_clears_pinning_so_propagate_returns_empty() {
    // pop() drops facts, so the (= x 6) propagation no longer fires.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let _a6 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.push();
    th.notify_fact(a3, true);
    assert!(!th.propagate().is_empty());
    th.pop();
    assert!(th.propagate().is_empty());
}
