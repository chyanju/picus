use super::*;

use std::collections::BTreeMap;

use num_bigint::BigUint;

use crate::cdclt::atoms::{AtomTable, InternResult};
use crate::frontend::encoder::PolyTerm;
use crate::sat::Solver;

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
) -> Var {
    let lhs = vec![t(vn, 1, &[var])];
    let rhs = vec![t(vn, c, &[])];
    match tbl.intern_eq(&lhs, &rhs, vn, sat) {
        InternResult::Var(v) => v,
        _ => panic!("expected Var"),
    }
}

#[test]
fn audit_eq_dedups_same_polynomial_atoms() {
    // Two atom variables built from EQUAL canonical polynomials (same
    // (lhs, rhs) up to canonicalisation) must collapse into one rep.
    // Asserting both with the same polarity should yield one Fresh and
    // one Redundant.
    let mut atoms_a = AtomTable::new(BigUint::from(7u32));
    let mut atoms_b = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn_a: Vec<String> = Vec::new();
    let mut vn_b: Vec<String> = Vec::new();
    let var_a = intern_eq_var(&mut atoms_a, &mut sat, &mut vn_a, "x", 3);
    let var_b = intern_eq_var(&mut atoms_b, &mut sat, &mut vn_b, "x", 3);
    let key_a = atoms_a.atom(var_a).expect("atom a present").clone();
    let key_b = atoms_b.atom(var_b).expect("atom b present").clone();

    let mut eq = EqualityEngine::new();
    eq.register_atom(var_a, &key_a);
    eq.register_atom(var_b, &key_b);

    assert_eq!(eq.notify(var_a, true), NotifyOutcome::Fresh);
    assert_eq!(eq.notify(var_b, true), NotifyOutcome::Redundant);
    assert_eq!(eq.n_fresh_polarities(), 1);
}

#[test]
fn audit_eq_detects_polarity_contradiction() {
    // Two atoms representing the same poly. Asserting them with opposite
    // polarity returns Contradiction on the second call.
    let mut atoms_a = AtomTable::new(BigUint::from(7u32));
    let mut atoms_b = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn_a: Vec<String> = Vec::new();
    let mut vn_b: Vec<String> = Vec::new();
    let var_a = intern_eq_var(&mut atoms_a, &mut sat, &mut vn_a, "x", 3);
    let var_b = intern_eq_var(&mut atoms_b, &mut sat, &mut vn_b, "x", 3);
    let key_a = atoms_a.atom(var_a).expect("atom a present").clone();
    let key_b = atoms_b.atom(var_b).expect("atom b present").clone();

    let mut eq = EqualityEngine::new();
    eq.register_atom(var_a, &key_a);
    eq.register_atom(var_b, &key_b);

    assert_eq!(eq.notify(var_a, true), NotifyOutcome::Fresh);
    assert_eq!(eq.notify(var_b, false), NotifyOutcome::Contradiction);
}

#[test]
fn audit_eq_distinct_polys_remain_distinct_reps() {
    // (x = 3) and (x = 4) canonicalise to different bytes; should stay in
    // separate union-find classes.
    let mut atoms = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn: Vec<String> = Vec::new();
    let var3 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 3);
    let var4 = intern_eq_var(&mut atoms, &mut sat, &mut vn, "x", 4);
    let key3 = atoms.atom(var3).expect("atom 3").clone();
    let key4 = atoms.atom(var4).expect("atom 4").clone();

    let mut eq = EqualityEngine::new();
    eq.register_atom(var3, &key3);
    eq.register_atom(var4, &key4);
    assert_eq!(eq.notify(var3, true), NotifyOutcome::Fresh);
    assert_eq!(eq.notify(var4, true), NotifyOutcome::Fresh);
    assert_eq!(eq.n_fresh_polarities(), 2);
}

#[test]
fn audit_eq_push_pop_restores_polarities() {
    // Assert, push, assert (same rep with conflicting polarity by virtue
    // of having registered an alias), pop, the conflict must be gone.
    let mut atoms_a = AtomTable::new(BigUint::from(7u32));
    let mut atoms_b = AtomTable::new(BigUint::from(7u32));
    let mut sat = Solver::new();
    let mut vn_a: Vec<String> = Vec::new();
    let mut vn_b: Vec<String> = Vec::new();
    let var_a = intern_eq_var(&mut atoms_a, &mut sat, &mut vn_a, "x", 3);
    let var_b = intern_eq_var(&mut atoms_b, &mut sat, &mut vn_b, "x", 3);
    let key_a = atoms_a.atom(var_a).expect("atom a").clone();
    let key_b = atoms_b.atom(var_b).expect("atom b").clone();

    let mut eq = EqualityEngine::new();
    eq.register_atom(var_a, &key_a);
    eq.register_atom(var_b, &key_b);

    assert_eq!(eq.notify(var_a, true), NotifyOutcome::Fresh);
    eq.push();
    // Pre-pop: notifying var_b with false would be a contradiction.
    assert_eq!(eq.notify(var_b, false), NotifyOutcome::Contradiction);
    eq.pop();
    // After pop the polarity recorded for the rep is restored to `true`
    // (set before push), so a same-polarity notification is Redundant.
    assert_eq!(eq.notify(var_a, true), NotifyOutcome::Redundant);
}

#[test]
fn audit_eq_term_order_canonicalisation_collapses_xy_and_yx() {
    // Build two atoms whose terms reference `[x, y]` vs `[y, x]`. Same
    // polynomial; canonicalisation must dedup.
    use crate::cdclt::atoms::AtomKey;
    let key_xy = AtomKey {
        terms: vec![
            (BigUint::from(1u32), vec!["x".to_string(), "y".to_string()]),
            (BigUint::from(2u32), vec!["x".to_string()]),
        ],
    };
    let key_yx = AtomKey {
        terms: vec![
            (BigUint::from(2u32), vec!["x".to_string()]),
            (BigUint::from(1u32), vec!["y".to_string(), "x".to_string()]),
        ],
    };
    let v1 = Var(0);
    let v2 = Var(1);
    let mut eq = EqualityEngine::new();
    eq.register_atom(v1, &key_xy);
    eq.register_atom(v2, &key_yx);
    assert_eq!(eq.notify(v1, true), NotifyOutcome::Fresh);
    assert_eq!(eq.notify(v2, true), NotifyOutcome::Redundant);
}
