use super::*;
use std::collections::BTreeMap;

use crate::cdclt::atoms::{AtomTable, InternResult};
use crate::frontend::encoder::PolyTerm;
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
    match th.post_check() {
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
    match th.post_check() {
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
    match th.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&av));
        }
        other => panic!("expected Unsat, got {:?}", other),
    }
}

#[test]
fn neq_distinct_atoms_core_is_precise() {
    // (= x 5) ∧ (= y 5) ∧ ¬(= x y): UNSAT. The conflict needs all
    // three facts (dropping any one is satisfiable), so the returned
    // core must be exactly {a1, a2, a3} — no dropped real atom, no
    // spurious atom. Exercises the disequality (Rabinowitsch) path with
    // *distinct* atoms, where positional index mapping would misattribute.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a1 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let a2 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 5);
    let a3 = intern_eq_terms(&mut atoms, &mut sat, &mut vn, &[(1, &["x"])], &[(1, &["y"])]);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a1, true);
    th.notify_fact(a2, true);
    th.notify_fact(a3, false);
    match th.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&a1), "core must keep x=5");
            assert!(core.contains(&a2), "core must keep y=5");
            assert!(core.contains(&a3), "core must keep x≠y");
            assert_eq!(core.len(), 3, "core must contain no spurious atoms: {:?}", core);
        }
        other => panic!("expected Unsat, got {:?}", other),
    }
}

#[test]
fn multi_diseq_exhausts_small_field() {
    // Over GF(3): ¬(= x 0) ∧ ¬(= x 1) ∧ ¬(= x 2). With the field
    // polynomial x^3 - x = 0 forcing x ∈ {0,1,2}, excluding all three is
    // UNSAT. Three disequalities stress `Rabinowitsch(d)` alignment for
    // d = 0,1,2; the core must contain all three excluding atoms.
    let prime = BigUint::from(3u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a0 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 0);
    let a1 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 1);
    let a2 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 2);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a0, false);
    th.notify_fact(a1, false);
    th.notify_fact(a2, false);
    match th.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&a0), "core must keep x≠0");
            assert!(core.contains(&a1), "core must keep x≠1");
            assert!(core.contains(&a2), "core must keep x≠2");
        }
        other => panic!("expected Unsat, got {:?}", other),
    }
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

#[test]
fn post_check_skips_fact_for_var_not_in_table() {
    // A fact whose atom variable is absent from the table (not aux, not
    // an interned atom) is skipped in check_full_with_mapping (the
    // `atom() == None` continue). With no other facts, `had_any` stays
    // false ⇒ Sat with an empty model.
    let prime = BigUint::from(101u32);
    let atoms = AtomTable::new(prime);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(Var(999), true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("expected Sat, got {:?}", other),
    }
    let m = th.collect_model().expect("empty model present");
    assert!(m.is_empty());
}

#[test]
fn post_check_unknown_when_cancelled_before_solve() {
    // A pre-cancelled token: encode succeeds, then the post-encode
    // cancellation check returns Unknown.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let av = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::cancelled();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(av, true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown on cancellation, got {:?}", other),
    }
    assert!(
        th.collect_model().is_none(),
        "no model after a cancelled check"
    );
}

#[test]
fn collect_model_is_none_after_unsat() {
    // After an UNSAT post_check, has_model is false ⇒ collect_model None.
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
    assert!(matches!(th.post_check(), CheckOutcome::Unsat { .. }));
    assert!(th.collect_model().is_none());
}

#[test]
fn pinned_vars_skips_fact_for_var_not_in_table() {
    // pinned_vars must skip a positive fact whose atom is not in the
    // table (the `atom() == None` continue) while still pinning a real
    // single-var equality alongside it.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(Var(999), true); // no atom ⇒ skipped
    th.notify_fact(a5, true);
    let pinned = th.pinned_vars();
    assert_eq!(pinned.len(), 1, "only x is pinned: {:?}", pinned);
    let (value, _src) = pinned.get("x").expect("x pinned");
    assert_eq!(value, &BigUint::from(5u32));
}

#[test]
fn tier2_source_skips_single_var_equality() {
    // A single-variable equality on the trail is never a Tier 2 source
    // (it is handled by pinning). With only (= x 3) asserted, Tier 2
    // yields nothing; the (= x 6) propagation comes solely from Tier 1.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let a6 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 6);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a3, true);
    let pinned = th.pinned_vars();
    // Tier 2 alone produces no propagations from a single-var source.
    let tier2 = th.compute_tier2(&pinned);
    assert!(
        tier2.is_empty(),
        "single-var-eq source must be skipped by Tier 2: {:?}",
        tier2
    );
    // Tier 1 still derives (= x 6) is False.
    let tier1 = th.compute_tier1(&pinned);
    assert!(
        tier1.iter().any(|&(v, p, _)| v == a6 && !p),
        "Tier 1 must derive (= x 6) False: {:?}",
        tier1
    );
}

#[test]
fn tier2_skips_when_unpinned_coefficient_cancels_to_zero() {
    // (x*y - 3*y = 0) under x=3: the unpinned y coefficient is
    // 1*3 + (p-3) = 0, so Tier 2 bails (no value can be derived).
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let _ay7 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 7);
    let asrc = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x", "y"])],
        &[(3, &["y"])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asrc, true);
    let pinned = th.pinned_vars();
    let tier2 = th.compute_tier2(&pinned);
    assert!(
        tier2.is_empty(),
        "zero unpinned coefficient must yield no Tier 2 propagation: {:?}",
        tier2
    );
}

#[test]
fn tier2_derives_zero_value_when_constant_residue_is_zero() {
    // (x + y = 3) under x=3: residue acc_const = 3 + (p-3) = 0, so
    // neg_c = 0 ⇒ y = 0. The (= y 0) atom propagates True.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay0 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 0);
    let asum = intern_eq_terms(
        &mut atoms,
        &mut sat,
        &mut vn,
        &[(1, &["x"]), (1, &["y"])],
        &[(3, &[])],
    );
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let props = th.propagate();
    assert!(
        props.iter().any(|&(v, p)| v == ay0 && p),
        "x+y=3 with x=3 must derive (= y 0) True: {:?}",
        props
    );
}

#[test]
fn tier2_skips_target_atom_already_on_trail() {
    // x=3 + (x+y=7) derives y=4. Both (= y 4) and (= y 5) are atoms over
    // y. (= y 4) is on the trail (asserted with negative polarity, so it
    // does not pin y), so Tier 2 skips it; only the untrailed (= y 5)
    // propagates as False.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let ax3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let ay4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "y", 4);
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
    th.notify_fact(ay4, false); // on trail but does NOT pin y
    th.notify_fact(asum, true);
    let pinned = th.pinned_vars();
    let tier2 = th.compute_tier2(&pinned);
    assert!(
        !tier2.iter().any(|&(v, _, _)| v == ay4),
        "Tier 2 must not re-propagate an on-trail target atom: {:?}",
        tier2
    );
    assert!(
        tier2.iter().any(|&(v, p, _)| v == ay5 && !p),
        "Tier 2 must derive (= y 5) False from y=4: {:?}",
        tier2
    );
}

#[test]
fn tier1_skips_constant_only_atom_not_on_trail() {
    // A constant-only atom (= 0 1) interns to a vars-empty key. It is NOT
    // asserted, so it is a live atom slot when x is pinned. Tier 1
    // evaluates its (constant) polynomial but its `used_vars` set is empty,
    // so it is skipped to avoid an empty-reason propagation — never appears
    // in the Tier 1 results.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let a_x5 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 5);
    let a_const = intern_eq_terms(&mut atoms, &mut sat, &mut vn, &[(0, &[])], &[(1, &[])]);
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(a_x5, true); // pins x = 5; a_const stays off-trail
    let pinned = th.pinned_vars();
    let tier1 = th.compute_tier1(&pinned);
    assert!(
        !tier1.iter().any(|&(v, _, _)| v == a_const),
        "constant-only off-trail atom must be skipped by Tier 1: {:?}",
        tier1
    );
}

#[test]
fn tier1_reason_cites_every_pinning_source_for_multi_var_atom() {
    // (x + y = 7) under x=3, y=4 reduces to 0 ⇒ atom True via Tier 1.
    // The reason must name both pinning sources (the `reason.push` arm runs
    // once per distinct pinning source backing the atom's variables).
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
    th.notify_fact(ay4, true);
    let pinned = th.pinned_vars();
    let tier1 = th.compute_tier1(&pinned);
    let entry = tier1
        .iter()
        .find(|&&(v, _, _)| v == asum)
        .expect("(x+y=7) must reduce under x=3,y=4");
    let (_, polarity, reason) = entry;
    assert!(*polarity, "x+y-7 = 0 ⇒ atom True");
    let reason_vars: std::collections::HashSet<Var> =
        reason.iter().map(|&(v, _)| v).collect();
    assert!(reason_vars.contains(&ax3), "reason must cite x=3: {:?}", reason);
    assert!(reason_vars.contains(&ay4), "reason must cite y=4: {:?}", reason);
}

#[test]
fn tier2_skips_source_fact_for_var_not_in_table() {
    // A positive fact whose atom variable is not interned (not aux, not a
    // known atom) is skipped as a Tier 2 source via the `atom() == None`
    // continue. A genuine multi-var source alongside it still propagates,
    // confirming the loop continues past the missing fact.
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
    th.notify_fact(Var(999), true); // no atom in table ⇒ Tier 2 source skip
    th.notify_fact(ax3, true);
    th.notify_fact(asum, true);
    let pinned = th.pinned_vars();
    let tier2 = th.compute_tier2(&pinned);
    assert!(
        tier2.iter().any(|&(v, p, _)| v == ay4 && p),
        "Tier 2 must still derive (= y 4) True despite the missing-atom fact: {:?}",
        tier2
    );
}

#[test]
fn post_check_unknown_when_encode_rejects_oversized_system() {
    // `encode` rejects any ring with more than 5000 variables
    // (`encode_impl`'s `n_vars > 5000` guard). A single multi-variable
    // equality atom spanning 5001 distinct variables interns 5001 names
    // into the builder, so the freshly built `ConstraintSystem` fails to
    // encode. `check_full_with_mapping` maps that `Err` to
    // `CheckOutcome::Unknown`.
    let prime = BigUint::from(101u32);
    let mut atoms = AtomTable::new(prime);
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    // Build an equality `v0 + v1 + ... + v5000 = 0` over 5001 distinct vars.
    let names: Vec<String> = (0..5001).map(|i| format!("v{}", i)).collect();
    let lhs: Vec<PolyTerm> = names.iter().map(|n| t(&mut vn, 1, &[n.as_str()])).collect();
    let rhs: Vec<PolyTerm> = vec![t(&mut vn, 0, &[])];
    let av = match atoms.intern_eq(&lhs, &rhs, &vn, &mut sat) {
        InternResult::Var(v) => v,
        other => panic!("expected Var, got {:?}", other),
    };
    let cancel = CancelToken::none();
    let mut th = FfTheory::new(&atoms, &cancel);
    th.notify_fact(av, true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown on encode rejection, got {:?}", other),
    }
    assert!(
        th.collect_model().is_none(),
        "no model when the encode step rejects the system"
    );
}

/// Build a real `EncodedSystem` with one equality (`x - 5 = 0`) and one
/// disequality (`x != 0`) so its provenance carries an `Equality(_)` and
/// a `Rabinowitsch(0)` entry.
fn encode_eq_and_diseq() -> EncodedSystem {
    let mut builder = ConstraintSystemBuilder::new(BigUint::from(101u32));
    let x = builder.var("x");
    // x - 5 = 0
    builder.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(x, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(96u32), // -5 mod 101
            vars: vec![],
        },
    ]);
    // x != 0: introduce d = x, assert d != __zero
    let mut seq = 0usize;
    let mut zero_idx: Option<u32> = None;
    let (d, zero) = builder.fresh_disequality_vars(&mut seq, &mut zero_idx);
    builder.add_equality(vec![
        PolyTerm {
            coeff: BigUint::from(1u32),
            vars: vec![(d, 1)],
        },
        PolyTerm {
            coeff: BigUint::from(100u32), // -1 mod 101
            vars: vec![(x, 1)],
        },
    ]);
    builder.add_disequality(d, zero);
    let indexed = builder.build();
    encode(&indexed).expect("encode succeeds")
}

/// First polynomial index in `encoded` whose provenance is an
/// `Equality(_)`.
fn first_equality_index(encoded: &EncodedSystem) -> usize {
    encoded
        .poly_provenance
        .iter()
        .position(|p| matches!(p, PolySource::Equality(_)))
        .expect("at least one Equality provenance")
}

/// First polynomial index in `encoded` whose provenance is a
/// `Rabinowitsch(_)`.
fn first_rabinowitsch_index(encoded: &EncodedSystem) -> usize {
    encoded
        .poly_provenance
        .iter()
        .position(|p| matches!(p, PolySource::Rabinowitsch(_)))
        .expect("at least one Rabinowitsch provenance")
}

#[test]
fn map_core_falls_back_to_full_trail_on_equality_misalignment() {
    // When n_input_equalities != equality_atoms.len(), an Equality(j)
    // core index cannot be precisely attributed ⇒ need_full ⇒ the full
    // trail (all equality + disequality atoms) is returned.
    let encoded = encode_eq_and_diseq();
    let eq_idx = first_equality_index(&encoded);
    // Deliberately misaligned: encoder saw `n_input_equalities` (>= 1)
    // equalities, but we pass an equality_atoms slice of a different len.
    assert_ne!(encoded.n_input_equalities, 3);
    let equality_atoms = vec![Var(0), Var(1), Var(2)];
    let disequality_atoms = vec![Var(5)];
    let core = map_core_to_atoms(&[eq_idx], &encoded, &equality_atoms, &disequality_atoms)
        .expect("full trail is non-empty");
    // Full trail = sorted/deduped union of equality + disequality atoms.
    let mut expected = equality_atoms.clone();
    expected.extend_from_slice(&disequality_atoms);
    expected.sort();
    expected.dedup();
    assert_eq!(core, expected);
}

#[test]
fn map_core_falls_back_when_rabinowitsch_index_out_of_range() {
    // A Rabinowitsch(d) core index with d beyond disequality_atoms.len()
    // forces the full-trail fallback.
    let encoded = encode_eq_and_diseq();
    // Keep the equality frame aligned so only the Rabinowitsch miss
    // triggers need_full.
    let n_eq = encoded.n_input_equalities;
    let equality_atoms: Vec<Var> = (0..n_eq as u32).map(Var).collect();
    let rab_idx = first_rabinowitsch_index(&encoded);
    // Empty disequality_atoms ⇒ disequality_atoms.get(0) is None.
    let core = map_core_to_atoms(&[rab_idx], &encoded, &equality_atoms, &[])
        .expect("full trail non-empty (equalities present)");
    assert_eq!(core, equality_atoms);
}

#[test]
fn map_core_returns_none_when_full_trail_is_empty() {
    // Core index maps to an `Other`/encoder-internal polynomial only, and
    // both atom slices are empty ⇒ atom_core empty ⇒ full trail empty ⇒
    // None.
    let encoded = encode_eq_and_diseq();
    // Find an `Other`/unattributable index if present; otherwise use an
    // index past the end (poly_provenance.get -> None branch).
    let other_idx = encoded
        .poly_provenance
        .iter()
        .position(|p| matches!(p, PolySource::Other))
        .unwrap_or(encoded.poly_provenance.len());
    let core = map_core_to_atoms(&[other_idx], &encoded, &[], &[]);
    assert!(core.is_none(), "empty full-trail fallback must be None");
}

#[test]
fn map_core_precise_when_equality_aligned() {
    // With n_input_equalities == equality_atoms.len() and an Equality(j)
    // core index, the precise atom (equality_atoms[j]) is returned.
    let encoded = encode_eq_and_diseq();
    let n_eq = encoded.n_input_equalities;
    // Distinct sentinel atom vars, one per input equality.
    let equality_atoms: Vec<Var> = (10..10 + n_eq as u32).map(Var).collect();
    let eq_idx = first_equality_index(&encoded);
    let j = match encoded.poly_provenance[eq_idx] {
        PolySource::Equality(j) => j,
        _ => unreachable!(),
    };
    let core = map_core_to_atoms(&[eq_idx], &encoded, &equality_atoms, &[])
        .expect("precise core present");
    assert_eq!(core, vec![equality_atoms[j]]);
}
