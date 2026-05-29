use super::*;
use crate::frontend::encoder::VarIdx;

/// Index-keyed term constructor for tests. `idx_vars` is a list
/// of `(VarIdx, exp)` pairs.
fn pt(coeff: u64, idx_vars: &[(VarIdx, u16)]) -> PolyTerm {
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars: idx_vars.to_vec(),
    }
}

/// Construct a single-name-keyed term list `coeff * x` for var
/// index 0 (the test's only variable). `vars = &[]` yields a
/// constant term.
fn t(coeff: u64, exp: u16) -> PolyTerm {
    if exp == 0 {
        pt(coeff, &[])
    } else {
        pt(coeff, &[(0, exp)])
    }
}

fn names(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| s.to_string()).collect()
}

#[test]
fn intern_same_eq_returns_same_var() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    let lhs = vec![t(1, 1)];
    let rhs = vec![t(0, 0)];
    let r1 = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
    let r2 = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
    match (r1, r2) {
        (InternResult::Var(v1), InternResult::Var(v2)) => assert_eq!(v1, v2),
        _ => panic!("expected two Var results"),
    }
    assert_eq!(sat.n_vars(), 1);
}

#[test]
fn intern_symmetric_eq_dedups() {
    // (= x y) and (= y x) must share one var.
    // var index 0 = x, index 1 = y.
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x", "y"]);
    let lhs_a = vec![pt(1, &[(0, 1)])]; // x
    let rhs_a = vec![pt(1, &[(1, 1)])]; // y
    let lhs_b = vec![pt(1, &[(1, 1)])]; // y
    let rhs_b = vec![pt(1, &[(0, 1)])]; // x
    let r1 = tbl.intern_eq(&lhs_a, &rhs_a, &vn, &mut sat);
    let r2 = tbl.intern_eq(&lhs_b, &rhs_b, &vn, &mut sat);
    match (r1, r2) {
        (InternResult::Var(v1), InternResult::Var(v2)) => assert_eq!(v1, v2),
        _ => panic!("expected two Var results"),
    }
}

#[test]
fn intern_trivial_eq() {
    // (= 0 0) → trivially true.
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn: Vec<String> = vec![];
    let lhs: Vec<PolyTerm> = vec![];
    let rhs: Vec<PolyTerm> = vec![];
    let r = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
    match r {
        InternResult::Trivial(b) => assert!(b),
        _ => panic!("expected Trivial(true)"),
    }
    assert_eq!(sat.n_vars(), 0);
}

#[test]
fn aux_var_distinct_from_atom_var() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    let r1 = tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
    let aux = tbl.new_aux(&mut sat);
    match r1 {
        InternResult::Var(v) => assert_ne!(v, aux),
        _ => panic!("expected Var"),
    }
    assert!(tbl.is_auxiliary(aux));
}

#[test]
fn single_var_eq_detected() {
    let prime = BigUint::from(101u32);
    let vn = names(&["x"]);
    // `(= x 0)` → canonical key for `x = 0`.
    let k0 = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(0, 0)], &vn, &prime);
    let (var, val) = k0.as_single_var_eq(&prime).expect("single-var-eq");
    assert_eq!(var, "x");
    assert_eq!(val, BigUint::zero());

    // `(= x 5)` → x = 5.
    let k5 = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(5, 0)], &vn, &prime);
    let (var, val) = k5.as_single_var_eq(&prime).expect("single-var-eq");
    assert_eq!(var, "x");
    assert_eq!(val, BigUint::from(5u32));

    // `(= x y)` (two variables) → None.
    let vn_xy = names(&["x", "y"]);
    let kxy = AtomKey::from_indexed_eq(&[pt(1, &[(0, 1)])], &[pt(1, &[(1, 1)])], &vn_xy, &prime);
    assert!(kxy.as_single_var_eq(&prime).is_none());

    // `(= (* x x) 0)` (degree 2) → None.
    let kxx = AtomKey::from_indexed_eq(&[t(1, 2)], &[t(0, 0)], &vn, &prime);
    assert!(kxx.as_single_var_eq(&prime).is_none());
}

#[test]
fn intern_eq_emits_mutex_clause_between_same_var_constants() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    let a0 = match tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!(),
    };
    let n_clauses_before = sat.n_clauses();
    let a1 = match tbl.intern_eq(&[t(1, 1)], &[t(1, 0)], &vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!(),
    };
    assert_ne!(a0, a1);
    assert!(sat.n_clauses() > n_clauses_before);
    assert!(sat.add_clause(vec![Lit::pos(a0)]));
    let added_second = sat.add_clause(vec![Lit::pos(a1)]);
    assert!(!added_second);
    assert!(sat.is_unsat());
}

#[test]
fn intern_eq_no_mutex_between_same_constant_repeats() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
    let n_clauses_before = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
    assert_eq!(sat.n_clauses(), n_clauses_before);
}

#[test]
fn intern_eq_no_mutex_across_different_variables() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x", "y"]);
    let ax = match tbl.intern_eq(&[pt(1, &[(0, 1)])], &[pt(0, &[])], &vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!(),
    };
    let ay = match tbl.intern_eq(&[pt(1, &[(1, 1)])], &[pt(0, &[])], &vn, &mut sat) {
        InternResult::Var(v) => v,
        _ => panic!(),
    };
    assert!(sat.add_clause(vec![Lit::pos(ax)]));
    assert!(sat.add_clause(vec![Lit::pos(ay)]));
    assert!(!sat.is_unsat());
}

#[test]
fn intern_eq_emits_three_pairwise_mutexes_for_three_constants() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    let n0 = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
    let n1 = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(1, 0)], &vn, &mut sat);
    let n2 = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(2, 0)], &vn, &mut sat);
    let n3 = sat.n_clauses();
    assert_eq!(n1 - n0, 0);
    assert_eq!(n2 - n1, 1);
    assert_eq!(n3 - n2, 2);
}

#[test]
fn mutex_invariant_under_lhs_rhs_swap() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(101u32));
    let vn = names(&["x"]);
    let r1 = tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
    let n_after_first = sat.n_clauses();
    let r2 = tbl.intern_eq(&[t(5, 0)], &[t(1, 1)], &vn, &mut sat);
    match (r1, r2) {
        (InternResult::Var(a), InternResult::Var(b)) => assert_eq!(a, b),
        _ => panic!("expected Var both times"),
    }
    assert_eq!(sat.n_clauses(), n_after_first);
}

#[test]
fn single_var_eq_detects_nonunit_coefficient_via_fermat() {
    let prime = BigUint::from(7u32);
    let vn = names(&["x"]);
    let k_direct = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(5, 0)], &vn, &prime);
    let (var_d, val_d) = k_direct.as_single_var_eq(&prime).expect("direct");
    assert_eq!(var_d, "x");
    assert_eq!(val_d, BigUint::from(5u32));
    let k_scaled = AtomKey::from_indexed_eq(&[t(2, 1)], &[t(3, 0)], &vn, &prime);
    let (var_s, val_s) = k_scaled.as_single_var_eq(&prime).expect("scaled");
    assert_eq!(var_s, "x");
    assert_eq!(val_s, BigUint::from(5u32));
}

#[test]
fn intern_eq_emits_mutex_across_semantically_distinct_scaled_atoms() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(7u32));
    let vn = names(&["x"]);
    let n0 = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
    let n1 = sat.n_clauses();
    assert_eq!(n1 - n0, 0);
    tbl.intern_eq(&[t(2, 1)], &[t(10, 0)], &vn, &mut sat);
    let n2 = sat.n_clauses();
    assert_eq!(n2 - n1, 0);
    tbl.intern_eq(&[t(1, 1)], &[t(6, 0)], &vn, &mut sat);
    let n3 = sat.n_clauses();
    assert_eq!(n3 - n2, 2);
}

#[test]
fn mutex_does_not_fire_for_equivalent_value_via_canonicalization() {
    let mut sat = Solver::new();
    let mut tbl = AtomTable::new(BigUint::from(7u32));
    let vn = names(&["x"]);
    tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
    let n_after = sat.n_clauses();
    tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
    assert_eq!(sat.n_clauses(), n_after);
    tbl.intern_eq(&[t(1, 1)], &[t(6, 0)], &vn, &mut sat);
    assert_eq!(sat.n_clauses(), n_after + 1);
}
