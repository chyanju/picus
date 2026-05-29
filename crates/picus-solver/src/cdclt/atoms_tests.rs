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

#[test]
fn as_single_var_eq_none_branches_for_unpinnable_shapes() {
    // Folded sweep over every AtomKey shape that `as_single_var_eq`
    // must reject (no single-var pin derivable):
    //   1. empty key (trivially-true 0 = 0)
    //   2. lone constant term (no variable)
    //   3. lone 0·x (zero/non-invertible coefficient)
    //   4. two-term 0·x + 3 = 0 (var-coeff is zero)
    //   5. two-term x + y = 0 (both terms carry variables)
    //   6. two-term x·y + 3 = 0 (var term names two variables — deg 2)
    let prime = BigUint::from(101u32);
    let cases: &[(&str, Vec<(BigUint, Vec<String>)>)] = &[
        ("empty", vec![]),
        ("lone-const", vec![(BigUint::from(5u32), vec![])]),
        ("lone-zero-coeff", vec![(BigUint::zero(), vec!["x".to_string()])]),
        (
            "two-term-zero-var-coeff",
            vec![
                (BigUint::from(3u32), vec![]),
                (BigUint::zero(), vec!["x".to_string()]),
            ],
        ),
        (
            "two-term-both-vars",
            vec![
                (BigUint::from(1u32), vec!["x".to_string()]),
                (BigUint::from(1u32), vec!["y".to_string()]),
            ],
        ),
        (
            "two-term-multivar-var",
            vec![
                (BigUint::from(3u32), vec![]),
                (BigUint::from(1u32), vec!["x".to_string(), "y".to_string()]),
            ],
        ),
    ];
    for (label, terms) in cases {
        let key = AtomKey { terms: terms.clone() };
        assert!(
            key.as_single_var_eq(&prime).is_none(),
            "{}: must be None",
            label
        );
    }
}

#[test]
fn as_single_var_eq_some_branches_for_pinnable_shapes() {
    // Folded sweep over the Some-arms `as_single_var_eq` must hit:
    //   1. lone `a·x = 0` (a≠0) ⇒ x = 0 (single-var arm).
    //   2. `a·x + 0 = 0` with a≠0 and zero constant ⇒ x = 0 (var-first /
    //      zero-constant branch — `from_indexed_eq` would never emit this
    //      ordering, but the public method must still handle a directly
    //      constructed key).
    //   3. `2·x + 3 = 0` over GF(7): x = (−3)·2⁻¹ = 4·4 = 16 mod 7 = 2
    //      (var-first nonzero-constant Fermat branch).
    let p101 = BigUint::from(101u32);
    let p7 = BigUint::from(7u32);
    let cases: &[(&str, &BigUint, Vec<(BigUint, Vec<String>)>, BigUint)] = &[
        (
            "lone-var",
            &p101,
            vec![(BigUint::from(7u32), vec!["x".to_string()])],
            BigUint::zero(),
        ),
        (
            "var-first-zero-const",
            &p101,
            vec![
                (BigUint::from(7u32), vec!["x".to_string()]),
                (BigUint::zero(), vec![]),
            ],
            BigUint::zero(),
        ),
        (
            "var-first-nonzero-const-fermat",
            &p7,
            vec![
                (BigUint::from(2u32), vec!["x".to_string()]),
                (BigUint::from(3u32), vec![]),
            ],
            BigUint::from(2u32),
        ),
    ];
    for (label, prime, terms, expected) in cases {
        let key = AtomKey { terms: terms.clone() };
        let (var, val) = key
            .as_single_var_eq(prime)
            .unwrap_or_else(|| panic!("{}: expected Some", label));
        assert_eq!(var, "x", "{}: var name", label);
        assert_eq!(&val, expected, "{}: value", label);
    }
}

#[test]
fn intern_negated_into_negates_coeffs() {
    // Terms `[(5, x), (0, const)]` over prime 101 negate to
    // `[(96, x), (0, const)]`: 96 = 101 - 5, zero stays zero.
    let prime = BigUint::from(101u32);
    let key = AtomKey {
        terms: vec![
            (BigUint::from(5u32), vec!["x".to_string()]),
            (BigUint::zero(), vec![]),
        ],
    };
    let mut builder = ConstraintSystemBuilder::new(prime.clone());
    let out = key.intern_negated_into(&mut builder, &prime);
    assert_eq!(out.len(), 2);
    // First term: 96·x where x is the first interned var (idx 0).
    assert_eq!(out[0].coeff, BigUint::from(96u32));
    assert_eq!(out[0].vars, vec![(0u32, 1u16)]);
    // Second term: constant 0, no variables.
    assert_eq!(out[1].coeff, BigUint::zero());
    assert!(out[1].vars.is_empty());
}

#[test]
fn intern_negated_into_collapses_repeated_names_to_exponent() {
    // Within-term `x * x` (vars = ["x", "x"]) collapses to (idx, 2);
    // a coeff of 3 negates to 101 - 3 = 98.
    let prime = BigUint::from(101u32);
    let key = AtomKey {
        terms: vec![(BigUint::from(3u32), vec!["x".to_string(), "x".to_string()])],
    };
    let mut builder = ConstraintSystemBuilder::new(prime.clone());
    let out = key.intern_negated_into(&mut builder, &prime);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].coeff, BigUint::from(98u32));
    assert_eq!(out[0].vars, vec![(0u32, 2u16)]);
}

#[test]
fn intern_result_into_lit_pos_var_and_trivial() {
    let v = crate::sat::Var(3);
    match InternResult::Var(v).into_lit_pos() {
        InternLit::Lit(l) => {
            assert_eq!(l.var(), v);
            assert!(l.is_positive());
        }
        _ => panic!("expected Lit"),
    }
    match InternResult::Trivial(true).into_lit_pos() {
        InternLit::Constant(b) => assert!(b),
        _ => panic!("expected Constant(true)"),
    }
    match InternResult::Trivial(false).into_lit_pos() {
        InternLit::Constant(b) => assert!(!b),
        _ => panic!("expected Constant(false)"),
    }
}

#[test]
fn intern_result_into_lit_neg_var_and_trivial() {
    let v = crate::sat::Var(2);
    match InternResult::Var(v).into_lit_neg() {
        InternLit::Lit(l) => {
            assert_eq!(l.var(), v);
            assert!(l.is_negative());
        }
        _ => panic!("expected Lit"),
    }
    // Negative polarity flips the trivial truth value.
    match InternResult::Trivial(true).into_lit_neg() {
        InternLit::Constant(b) => assert!(!b),
        _ => panic!("expected Constant(false)"),
    }
    match InternResult::Trivial(false).into_lit_neg() {
        InternLit::Constant(b) => assert!(b),
        _ => panic!("expected Constant(true)"),
    }
}
