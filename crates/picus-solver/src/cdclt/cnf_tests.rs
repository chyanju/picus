use super::*;
use crate::boolean::{Formula, Literal};
use crate::frontend::encoder::PolyTerm;
use crate::sat::LBool;
use crate::sat::solver::SolveResult;
use num_bigint::BigUint;

/// Construct a literal `coeff * var_name == rhs_const` where
/// `var_name`'s VarIdx is `var_idx`. `var_names` is the fixture
/// frame; the caller pre-allocates `var_names = ["x", "y", "z"]`
/// and uses indices 0/1/2.
fn lit_eq(coeff_lhs: u64, var_idx: u32, rhs_const: u64) -> Formula {
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
fn single_eq_atom() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x"]);
    let f = lit_eq(1, 0, 0);
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    match r {
        TseitinResult::Lit(l) => {
            assert!(l.is_positive());
            assert_eq!(sat.n_vars(), 1);
        }
        _ => panic!("expected Lit"),
    }
}

#[test]
fn and_of_two_atoms_sat() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x", "y"]);
    let f = Formula::And(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 0)]);
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    if let TseitinResult::Lit(top) = r {
        assert!(sat.add_clause(vec![top]));
        assert_eq!(sat.solve(), SolveResult::Sat);
    } else {
        panic!("expected Lit");
    }
}

#[test]
fn or_of_eq_neq_same_atom_is_true() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x"]);
    let f = Formula::Or(vec![
        lit_eq(1, 0, 0),
        Formula::Not(Box::new(lit_eq(1, 0, 0))),
    ]);
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    match r {
        TseitinResult::Constant(true) => {}
        TseitinResult::Lit(top) => {
            assert!(sat.add_clause(vec![top]));
            assert_eq!(sat.solve(), SolveResult::Sat);
        }
        TseitinResult::Constant(false) => panic!("tautology cannot be false"),
    }
}

#[test]
fn unsat_top_constant_false() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x"]);
    let f = Formula::And(vec![
        lit_eq(1, 0, 0),
        Formula::Not(Box::new(lit_eq(1, 0, 0))),
    ]);
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    match r {
        TseitinResult::Lit(top) => {
            let added = sat.add_clause(vec![top]);
            if added {
                assert_eq!(sat.solve(), SolveResult::Unsat);
            } else {
                assert!(sat.is_unsat());
            }
        }
        TseitinResult::Constant(false) => {}
        TseitinResult::Constant(true) => panic!("contradiction cannot be true"),
    }
}

#[test]
fn double_negation_flat() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x"]);
    let f = Formula::Not(Box::new(Formula::Not(Box::new(lit_eq(1, 0, 0)))));
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    if let TseitinResult::Lit(l) = r {
        assert!(l.is_positive());
        assert_eq!(sat.n_vars(), 1);
    } else {
        panic!("expected Lit");
    }
}

#[test]
fn not_constant_flips_truth_value() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn: Vec<String> = vec![];
    let r_true = tseitin(
        &Formula::Not(Box::new(Formula::True)),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(r_true, TseitinResult::Constant(false)));
    let r_false = tseitin(
        &Formula::Not(Box::new(Formula::False)),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(r_false, TseitinResult::Constant(true)));
    assert_eq!(sat.n_vars(), 0);
    assert_eq!(sat.n_clauses(), 0);
}

#[test]
fn trivially_true_atom_folds_to_constant() {
    // `(= 0 0)` interns to a trivially-true atom; positive polarity
    // folds to Constant(true), negation to Constant(false).
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn: Vec<String> = vec![];
    let triv = Formula::Lit(Literal::Eq(vec![], vec![]));
    let r = tseitin(&triv, &vn, &mut atoms, &mut sat);
    assert!(matches!(r, TseitinResult::Constant(true)));
    let r_neg = tseitin(
        &Formula::Not(Box::new(Formula::Lit(Literal::Eq(vec![], vec![])))),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(r_neg, TseitinResult::Constant(false)));
    assert_eq!(sat.n_vars(), 0);
    assert_eq!(sat.n_clauses(), 0);
}

#[test]
fn and_or_all_neutral_children_fold_to_identity() {
    // Folded symmetry: `And([T,T]) → Constant(true)` and `Or([F,F]) →
    // Constant(false)` exercise the all-neutral fold arm of each
    // connective; neither emits any SAT vars or clauses.
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn: Vec<String> = vec![];
    let and_r = tseitin(
        &Formula::And(vec![Formula::True, Formula::True]),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(and_r, TseitinResult::Constant(true)));
    let or_r = tseitin(
        &Formula::Or(vec![Formula::False, Formula::False]),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(or_r, TseitinResult::Constant(false)));
    assert_eq!(sat.n_vars(), 0);
    assert_eq!(sat.n_clauses(), 0);
}

#[test]
fn and_or_drop_neutral_and_return_single_remaining_lit() {
    // Folded symmetry: `And([True, lit])` and `Or([False, lit])` both
    // reduce to the lone `lit` with no auxiliary Tseitin variable
    // (drop-neutral arm of both connectives).
    let cases: &[(&str, Formula)] = &[
        (
            "And-drops-True",
            Formula::And(vec![Formula::True, lit_eq(1, 0, 5)]),
        ),
        (
            "Or-drops-False",
            Formula::Or(vec![Formula::False, lit_eq(1, 0, 5)]),
        ),
    ];
    for (label, f) in cases {
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let vn = names(&["x"]);
        let r = tseitin(f, &vn, &mut atoms, &mut sat);
        match r {
            TseitinResult::Lit(l) => {
                assert!(l.is_positive(), "{}: positive lit", label);
                assert_eq!(sat.n_vars(), 1, "{}: atom var only", label);
                assert!(!atoms.is_auxiliary(l.var()), "{}: no aux", label);
            }
            _ => panic!("{}: expected Lit", label),
        }
        assert_eq!(sat.n_clauses(), 0, "{}: no clauses emitted", label);
    }
}

#[test]
fn and_or_short_circuit_on_absorbing_child() {
    // Folded symmetry: `And([lit, False])` short-circuits to
    // Constant(false); `Or([True, lit])` short-circuits to Constant(true).
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x"]);
    let and_r = tseitin(
        &Formula::And(vec![lit_eq(1, 0, 5), Formula::False]),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(and_r, TseitinResult::Constant(false)));
    let or_r = tseitin(
        &Formula::Or(vec![Formula::True, lit_eq(1, 0, 5)]),
        &vn,
        &mut atoms,
        &mut sat,
    );
    assert!(matches!(or_r, TseitinResult::Constant(true)));
}

#[test]
fn lit_value_consistency_after_solve() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn = names(&["x", "y", "z"]);
    let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 0), lit_eq(1, 2, 0)]);
    let r = tseitin(&f, &vn, &mut atoms, &mut sat);
    if let TseitinResult::Lit(top) = r {
        assert!(sat.add_clause(vec![top]));
        assert_eq!(sat.solve(), SolveResult::Sat);
        let mut any_true = false;
        for v_idx in 0..sat.n_vars() {
            let v = crate::sat::Var(v_idx as u32);
            if !atoms.is_auxiliary(v) && sat.lit_value(Lit::pos(v)) == LBool::True {
                any_true = true;
            }
        }
        assert!(any_true);
    } else {
        panic!("expected Lit");
    }
}
