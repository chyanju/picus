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
fn true_folds() {
    let mut atoms = AtomTable::new(BigUint::from(101u32));
    let mut sat = Solver::new();
    let vn: Vec<String> = vec![];
    let r = tseitin(&Formula::True, &vn, &mut atoms, &mut sat);
    match r {
        TseitinResult::Constant(true) => {}
        _ => panic!("expected Constant(true)"),
    }
    assert_eq!(sat.n_vars(), 0);
    assert_eq!(sat.n_clauses(), 0);
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
