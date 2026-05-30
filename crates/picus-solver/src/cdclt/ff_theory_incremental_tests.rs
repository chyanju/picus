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
fn audit_inc_root_conflict_unsat_via_trivial_basis() {
    // Over GF(7): assert (x = 3) ∧ (x = 4). Together they imply 0 = -1,
    // so the IncrementalGB basis reduces to {1} and post_check returns
    // Unsat with both facts in the core.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v3, true);
    th.notify_fact(v4, true);
    match th.post_check() {
        CheckOutcome::Unsat { core } => {
            assert!(core.contains(&v3) && core.contains(&v4), "core must include both atoms");
        }
        other => panic!("expected UNSAT, got {:?}", other),
    }
    assert!(th.collect_model().is_none(), "no model on UNSAT");
}

#[test]
fn audit_inc_single_eq_is_sat_small_prime() {
    // Over GF(7): a single (x = 3). Basis is non-trivial → SAT (the
    // field-poly injection ensures GF(7)-membership; model extraction
    // deferred — we only assert the verdict shape).
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v, true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn audit_inc_push_pop_restores_basis() {
    // Assert (x=3), push, assert (x=4) → UNSAT, pop, post_check should be
    // SAT again because the contradiction was popped out.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let v4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.notify_fact(v3, true);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("pre-push SAT expected, got {:?}", other),
    }
    th.push();
    th.notify_fact(v4, true);
    match th.post_check() {
        CheckOutcome::Unsat { .. } => {}
        other => panic!("expected UNSAT after second assert, got {:?}", other),
    }
    th.pop();
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("post-pop SAT expected, got {:?}", other),
    }
}

#[test]
fn bug_inc_pop_restores_slot_claims_gf5() {
    // Over GF(5), 2 is a non-residue (squares = {0, 1, 4}), so x^2 = 2 is
    // UNSAT. The sequence push; (x = 0); pop; push; (x^2 = 2) must
    // re-inject the field polynomial x^5 - x for the reclaimed slot;
    // otherwise post_check sees only {x^2 - 2}, judges the basis
    // non-trivial, and (with add_field_polys=true for prime <= 1000)
    // returns Sat for an UNSAT input.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(5u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let v_x_eq_0 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 0);
    let lhs = vec![t(&mut vn, 1, &["x", "x"])];
    let rhs = vec![t(&mut vn, 2, &[])];
    let v_x2_eq_2 = match atoms.intern_eq(&lhs, &rhs, &mut vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    };

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 64);
    th.push();
    th.notify_fact(v_x_eq_0, true);
    th.pop();
    th.push();
    th.notify_fact(v_x2_eq_2, true);
    match th.post_check() {
        CheckOutcome::Sat => panic!(
            "x^2 = 2 over GF(5) is UNSAT; post_check returned Sat — slot claim leaked past pop"
        ),
        CheckOutcome::Unsat { .. } | CheckOutcome::Unknown => {}
    }
}

#[test]
fn bug_inc_notify_fact_slot_budget_exhausted_returns_unknown() {
    // max_vars=1 with an atom that mentions two distinct vars forces
    // slot-budget exhaustion in build_atom_polys. notify_fact must NOT
    // push the half-encoded fact onto the trail; post_check must return
    // Unknown (not Sat) because the trail no longer reflects the algebraic
    // state in the IGB.
    let cancel = CancelToken::none();
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    // Atom: x + y = 0 (two distinct variable names).
    let lhs = vec![t(&mut vn, 1, &["x"]), t(&mut vn, 1, &["y"])];
    let rhs = vec![t(&mut vn, 0, &[])];
    let atom_var = match atoms.intern_eq(&lhs, &rhs, &mut vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    };

    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 1);
    th.notify_fact(atom_var, true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown under slot-budget exhaustion, got {:?}", other),
    }
}

#[test]
fn bug_inc_notify_fact_unknown_atom_returns_unknown() {
    // Atom var not registered in AtomTable: build_atom_polys returns
    // None, notify_fact sets the degraded flag, post_check returns
    // Unknown rather than the Sat-on-empty-trail short-circuit.
    let cancel = CancelToken::none();
    let atoms = AtomTable::new(BigUint::from(7u32));
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    // Var(999) is not in the AtomTable.
    th.notify_fact(crate::sat::Var(999), true);
    match th.post_check() {
        CheckOutcome::Unknown => {}
        other => panic!("expected Unknown for unregistered atom, got {:?}", other),
    }
}

#[test]
fn audit_inc_empty_trail_is_sat() {
    let cancel = CancelToken::none();
    let atoms = AtomTable::new(BigUint::from(7u32));
    let mut th = IncrementalFfTheoryState::new(&atoms, &cancel, 16);
    match th.post_check() {
        CheckOutcome::Sat => {}
        other => panic!("empty trail SAT expected, got {:?}", other),
    }
    let m = th.collect_model().expect("empty model present");
    assert!(m.is_empty());
}
