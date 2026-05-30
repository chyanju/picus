use super::*;

use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::cdclt::atoms::{AtomTable, InternResult};
use crate::cdclt::theory::{CheckOutcome, Theory};
use crate::frontend::encoder::PolyTerm;
use crate::sat::Solver;
use crate::timeout::CancelToken;

fn ensure_var(vn: &mut Vec<String>, name: &str) -> u32 {
    if let Some(i) = vn.iter().position(|n| n == name) {
        return i as u32;
    }
    vn.push(name.to_string());
    (vn.len() - 1) as u32
}

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

fn intern_eq_var(
    tbl: &mut AtomTable,
    sat: &mut Solver,
    vn: &mut Vec<String>,
    var: &str,
    c: u64,
) -> crate::sat::Var {
    let lhs = vec![t(vn, 1, &[var])];
    let rhs = vec![t(vn, c, &[])];
    match tbl.intern_eq(&lhs, &rhs, vn, sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    }
}

#[test]
fn prop_router_partitions_facts_and_unions_sat() {
    // Two distinct primes; each has one atom that is satisfiable on its
    // own. Combined verdict must be SAT.
    let cancel = CancelToken::none();
    let atoms_gf7 = AtomTable::new(BigUint::from(7u32));
    let atoms_gf11 = AtomTable::new(BigUint::from(11u32));
    let mut router = FfTheoryRouter::new(vec![atoms_gf7, atoms_gf11], &cancel);
    assert_eq!(router.n_primes(), 2);
    assert_eq!(router.slot_idx_for(&BigUint::from(7u32)), Some(0));
    assert_eq!(router.slot_idx_for(&BigUint::from(11u32)), Some(1));
    assert_eq!(router.slot_idx_for(&BigUint::from(13u32)), None);

    let mut sat = Solver::new();
    let mut vn_a: Vec<String> = Vec::new();
    let mut vn_b: Vec<String> = Vec::new();
    let var_a = intern_eq_var(router.slot_atoms_mut(0), &mut sat, &mut vn_a, "a", 3);
    let var_b = intern_eq_var(router.slot_atoms_mut(1), &mut sat, &mut vn_b, "b", 5);
    router.assign_var(var_a, 0);
    router.assign_var(var_b, 1);

    router.notify_fact(var_a, true); // a = 3 over GF(7)
    router.notify_fact(var_b, true); // b = 5 over GF(11)

    let outcome = router.post_check();
    match outcome {
        CheckOutcome::Sat => {}
        other => panic!("expected SAT, got {:?}", other),
    }

    let model = router.collect_model().expect("model present");
    assert_eq!(model.get("a"), Some(&BigUint::from(3u32)));
    assert_eq!(model.get("b"), Some(&BigUint::from(5u32)));
}

#[test]
fn prop_router_unsat_in_one_slot_yields_unsat() {
    // GF(7) slot asserts a=3 ∧ a=4 (UNSAT). GF(11) slot is empty (SAT).
    // Combined verdict UNSAT; combined core comes from the GF(7) slot.
    let cancel = CancelToken::none();
    let atoms_gf7 = AtomTable::new(BigUint::from(7u32));
    let atoms_gf11 = AtomTable::new(BigUint::from(11u32));
    let mut router = FfTheoryRouter::new(vec![atoms_gf7, atoms_gf11], &cancel);

    let mut sat = Solver::new();
    let mut vn_a: Vec<String> = Vec::new();
    let var_a_eq3 = intern_eq_var(router.slot_atoms_mut(0), &mut sat, &mut vn_a, "a", 3);
    let var_a_eq4 = intern_eq_var(router.slot_atoms_mut(0), &mut sat, &mut vn_a, "a", 4);
    router.assign_var(var_a_eq3, 0);
    router.assign_var(var_a_eq4, 0);
    router.notify_fact(var_a_eq3, true);
    router.notify_fact(var_a_eq4, true);

    match router.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(!core.is_empty(), "UNSAT core must be non-empty");
            assert!(
                core.iter().all(|v| *v == var_a_eq3 || *v == var_a_eq4),
                "core must consist of GF(7) slot atoms"
            );
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
    assert!(router.collect_model().is_none(), "no model on UNSAT");
}

#[test]
fn prop_router_push_pop_restores_per_slot_trails() {
    // Push, add fact to slot 0, pop. Per-slot trail must be restored.
    let cancel = CancelToken::none();
    let atoms_gf7 = AtomTable::new(BigUint::from(7u32));
    let atoms_gf11 = AtomTable::new(BigUint::from(11u32));
    let mut router = FfTheoryRouter::new(vec![atoms_gf7, atoms_gf11], &cancel);

    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let var_a = intern_eq_var(router.slot_atoms_mut(0), &mut sat, &mut vn, "a", 3);
    router.assign_var(var_a, 0);

    router.push();
    router.notify_fact(var_a, true);
    // SAT before pop.
    match router.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("pre-pop should be SAT, got {:?}", other),
    }
    router.pop();
    // After pop, no facts; SAT (empty problem).
    match router.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("post-pop should be SAT, got {:?}", other),
    }
}

#[test]
fn bug_router_unregistered_fact_degrades_to_unknown_not_sat() {
    // A fact whose `Var` has not been assign_var'd cannot reach any
    // per-prime slot. Silently dropping it would let an UNSAT-producing
    // fact vanish, leaving the slot-union Sat for an unsatisfiable
    // problem. notify_fact must flip the degraded flag so post_check
    // returns Unknown.
    let cancel = CancelToken::none();
    let atoms_gf7 = AtomTable::new(BigUint::from(7u32));
    let mut router = FfTheoryRouter::new(vec![atoms_gf7], &cancel);

    let unregistered = crate::sat::Var(42);
    router.notify_fact(unregistered, true);
    match router.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown under unregistered-var degradation, got {:?}", other),
    }
}

#[test]
fn bug_router_pop_restores_degraded_flag() {
    // push; notify_fact(unregistered) at level 1 sets degraded; pop
    // restores degraded to its pre-push value (false), so the next
    // post_check on an empty trail returns Sat rather than the
    // post-degradation Unknown.
    let cancel = CancelToken::none();
    let atoms_gf7 = AtomTable::new(BigUint::from(7u32));
    let mut router = FfTheoryRouter::new(vec![atoms_gf7], &cancel);

    router.push();
    router.notify_fact(crate::sat::Var(99), true);
    match router.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("pre-pop should be Unknown after degradation, got {:?}", other),
    }
    router.pop();
    match router.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("post-pop should be Sat (degraded cleared), got {:?}", other),
    }
}
