//! Tseitin transformation: `Formula` → CNF clauses + top-level literal.
//!
//! Each non-leaf Boolean node introduces a fresh auxiliary SAT
//! variable `t` and adds clauses encoding `t ↔ child`. Leaves
//! (`Lit(Eq(_,_))` / `Lit(Neq(_,_))`) intern through [`AtomTable`].
//! `True` / `False` constants are folded statically so they never
//! reach the SAT solver.

use crate::boolean::{Formula, Literal};
use crate::sat::{Lit, Solver};

use super::atoms::{AtomTable, InternLit};

/// Apply Tseitin to `formula`, registering atoms in `atoms` and
/// emitting clauses into `sat`. `var_names` is the producing
/// builder's variable frame, used by [`AtomTable::intern_eq`] to
/// reverse-resolve `PolyTerm` indices to names for the canonical
/// `AtomKey`. Returns `TseitinResult` describing the formula's
/// top-level value: a SAT literal (assert as a unit clause to
/// require the formula true), or a constant.
pub fn tseitin(
    formula: &Formula,
    var_names: &[String],
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> TseitinResult {
    match transform(formula, var_names, atoms, sat) {
        Node::Lit(l) => TseitinResult::Lit(l),
        Node::Constant(b) => TseitinResult::Constant(b),
    }
}

/// Result of applying [`tseitin`].
#[derive(Debug)]
pub enum TseitinResult {
    /// Formula's truth value is the SAT literal. To assert the
    /// formula, add `[lit]` as a unit clause via `sat.add_clause`.
    Lit(Lit),
    /// Formula simplified to a constant truth value during the
    /// transformation. `Constant(true)` means trivially SAT;
    /// `Constant(false)` means trivially UNSAT.
    Constant(bool),
}

#[derive(Debug, Clone, Copy)]
enum Node {
    Lit(Lit),
    Constant(bool),
}

fn transform(
    f: &Formula,
    var_names: &[String],
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> Node {
    match f {
        Formula::True => Node::Constant(true),
        Formula::False => Node::Constant(false),
        Formula::Lit(Literal::Eq(a, b)) => atom_to_node(a, b, var_names, true, atoms, sat),
        Formula::Lit(Literal::Neq(a, b)) => atom_to_node(a, b, var_names, false, atoms, sat),
        Formula::Not(inner) => match transform(inner, var_names, atoms, sat) {
            Node::Lit(l) => Node::Lit(-l),
            Node::Constant(b) => Node::Constant(!b),
        },
        Formula::And(children) => transform_and(children, var_names, atoms, sat),
        Formula::Or(children) => transform_or(children, var_names, atoms, sat),
    }
}

fn atom_to_node(
    lhs: &[crate::encoder::PolyTerm],
    rhs: &[crate::encoder::PolyTerm],
    var_names: &[String],
    positive: bool,
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> Node {
    let result = atoms.intern_eq(lhs, rhs, var_names, sat);
    let il = if positive {
        result.into_lit_pos()
    } else {
        result.into_lit_neg()
    };
    match il {
        InternLit::Lit(l) => Node::Lit(l),
        InternLit::Constant(b) => Node::Constant(b),
    }
}

fn transform_and(
    children: &[Formula],
    var_names: &[String],
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> Node {
    // Constant-fold: any False child ⇒ whole conjunction is False.
    // Drop True children; on remaining literals build a Tseitin
    // equivalence `t ↔ (l1 ∧ ... ∧ lk)`.
    let mut lits: Vec<Lit> = Vec::with_capacity(children.len());
    for c in children {
        match transform(c, var_names, atoms, sat) {
            Node::Constant(true) => {}
            Node::Constant(false) => return Node::Constant(false),
            Node::Lit(l) => lits.push(l),
        }
    }
    if lits.is_empty() {
        return Node::Constant(true);
    }
    if lits.len() == 1 {
        return Node::Lit(lits[0]);
    }
    let t = atoms.new_aux(sat);
    let t_lit = Lit::pos(t);
    // t → li, for each i.
    for &l in &lits {
        let ok = sat.add_clause(vec![-t_lit, l]);
        debug_assert!(ok, "Tseitin clause must not be UNSAT at root");
    }
    // (∧ li) → t, i.e. (¬l1 ∨ ¬l2 ∨ ... ∨ t).
    let mut clause: Vec<Lit> = lits.iter().map(|l| -*l).collect();
    clause.push(t_lit);
    let ok = sat.add_clause(clause);
    debug_assert!(ok, "Tseitin clause must not be UNSAT at root");
    Node::Lit(t_lit)
}

fn transform_or(
    children: &[Formula],
    var_names: &[String],
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> Node {
    // Constant-fold: any True child ⇒ whole disjunction is True.
    // Drop False children; on remaining literals build `t ↔ (l1 ∨ ... ∨ lk)`.
    let mut lits: Vec<Lit> = Vec::with_capacity(children.len());
    for c in children {
        match transform(c, var_names, atoms, sat) {
            Node::Constant(true) => return Node::Constant(true),
            Node::Constant(false) => {}
            Node::Lit(l) => lits.push(l),
        }
    }
    if lits.is_empty() {
        return Node::Constant(false);
    }
    if lits.len() == 1 {
        return Node::Lit(lits[0]);
    }
    let t = atoms.new_aux(sat);
    let t_lit = Lit::pos(t);
    // li → t, for each i.
    for &l in &lits {
        let ok = sat.add_clause(vec![-l, t_lit]);
        debug_assert!(ok, "Tseitin clause must not be UNSAT at root");
    }
    // t → (∨ li), i.e. (¬t ∨ l1 ∨ ... ∨ lk).
    let mut clause: Vec<Lit> = vec![-t_lit];
    clause.extend(lits.iter().copied());
    let ok = sat.add_clause(clause);
    debug_assert!(ok, "Tseitin clause must not be UNSAT at root");
    Node::Lit(t_lit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolean::{Formula, Literal};
    use crate::encoder::PolyTerm;
    use crate::sat::solver::SolveResult;
    use crate::sat::LBool;
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
}
