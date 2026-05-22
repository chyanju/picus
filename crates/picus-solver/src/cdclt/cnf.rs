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
/// emitting clauses into `sat`. Returns `TseitinResult` describing
/// the formula's top-level value: a SAT literal (assert as a unit
/// clause to require the formula true), or a constant.
pub fn tseitin(
    formula: &Formula,
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> TseitinResult {
    match transform(formula, atoms, sat) {
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

fn transform(f: &Formula, atoms: &mut AtomTable, sat: &mut Solver) -> Node {
    match f {
        Formula::True => Node::Constant(true),
        Formula::False => Node::Constant(false),
        Formula::Lit(Literal::Eq(a, b)) => atom_to_node(a, b, true, atoms, sat),
        Formula::Lit(Literal::Neq(a, b)) => atom_to_node(a, b, false, atoms, sat),
        Formula::Not(inner) => match transform(inner, atoms, sat) {
            Node::Lit(l) => Node::Lit(-l),
            Node::Constant(b) => Node::Constant(!b),
        },
        Formula::And(children) => transform_and(children, atoms, sat),
        Formula::Or(children) => transform_or(children, atoms, sat),
    }
}

fn atom_to_node(
    lhs: &[crate::encoder::PolyTerm],
    rhs: &[crate::encoder::PolyTerm],
    positive: bool,
    atoms: &mut AtomTable,
    sat: &mut Solver,
) -> Node {
    let result = atoms.intern_eq(lhs, rhs, sat);
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

fn transform_and(children: &[Formula], atoms: &mut AtomTable, sat: &mut Solver) -> Node {
    // Constant-fold: any False child ⇒ whole conjunction is False.
    // Drop True children; on remaining literals build a Tseitin
    // equivalence `t ↔ (l1 ∧ ... ∧ lk)`.
    let mut lits: Vec<Lit> = Vec::with_capacity(children.len());
    for c in children {
        match transform(c, atoms, sat) {
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

fn transform_or(children: &[Formula], atoms: &mut AtomTable, sat: &mut Solver) -> Node {
    // Constant-fold: any True child ⇒ whole disjunction is True.
    // Drop False children; on remaining literals build `t ↔ (l1 ∨ ... ∨ lk)`.
    let mut lits: Vec<Lit> = Vec::with_capacity(children.len());
    for c in children {
        match transform(c, atoms, sat) {
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

    fn t(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn lit_eq(coeff_lhs: u64, var: &str, rhs_const: u64) -> Formula {
        Formula::Lit(Literal::Eq(
            vec![t(coeff_lhs, &[var])],
            vec![t(rhs_const, &[])],
        ))
    }

    #[test]
    fn true_folds() {
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let r = tseitin(&Formula::True, &mut atoms, &mut sat);
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
        let f = lit_eq(1, "x", 0);
        let r = tseitin(&f, &mut atoms, &mut sat);
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
        // (and (= x 0) (= y 0)): with the unit assertion that the
        // top-level lit is true, SAT must find values for both atoms.
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let f = Formula::And(vec![lit_eq(1, "x", 0), lit_eq(1, "y", 0)]);
        let r = tseitin(&f, &mut atoms, &mut sat);
        if let TseitinResult::Lit(top) = r {
            assert!(sat.add_clause(vec![top]));
            assert_eq!(sat.solve(), SolveResult::Sat);
        } else {
            panic!("expected Lit");
        }
    }

    #[test]
    fn or_of_eq_neq_same_atom_is_true() {
        // (or (= x 0) (not (= x 0))): tautology — should fold or SAT trivially.
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let f = Formula::Or(vec![
            lit_eq(1, "x", 0),
            Formula::Not(Box::new(lit_eq(1, "x", 0))),
        ]);
        let r = tseitin(&f, &mut atoms, &mut sat);
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
        // (and (= x 0) (not (= x 0))): contradiction. The canonical
        // atom interns to one SAT var; the two child literals are
        // SAT-level complements, so the SAT layer detects UNSAT.
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let f = Formula::And(vec![
            lit_eq(1, "x", 0),
            Formula::Not(Box::new(lit_eq(1, "x", 0))),
        ]);
        let r = tseitin(&f, &mut atoms, &mut sat);
        match r {
            TseitinResult::Lit(top) => {
                // `add_clause` may return false (root-level conflict
                // detected immediately) or true (solve must run).
                // Either way the formula is UNSAT.
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
        // ¬(¬(= x 0))  ≡  (= x 0)
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let f = Formula::Not(Box::new(Formula::Not(Box::new(lit_eq(1, "x", 0)))));
        let r = tseitin(&f, &mut atoms, &mut sat);
        if let TseitinResult::Lit(l) = r {
            assert!(l.is_positive());
            // Only one var: no auxiliaries needed.
            assert_eq!(sat.n_vars(), 1);
        } else {
            panic!("expected Lit");
        }
    }

    #[test]
    fn lit_value_consistency_after_solve() {
        // 3-atom disjunction: at least one must be true at the SAT level.
        let mut atoms = AtomTable::new(BigUint::from(101u32));
        let mut sat = Solver::new();
        let f = Formula::Or(vec![
            lit_eq(1, "x", 0),
            lit_eq(1, "y", 0),
            lit_eq(1, "z", 0),
        ]);
        let r = tseitin(&f, &mut atoms, &mut sat);
        if let TseitinResult::Lit(top) = r {
            assert!(sat.add_clause(vec![top]));
            assert_eq!(sat.solve(), SolveResult::Sat);
            // At least one of the three atom vars must be assigned True.
            // (The auxiliary top var is also True by construction.)
            let mut any_true = false;
            for v_idx in 0..sat.n_vars() {
                let v = crate::sat::Var(v_idx as u32);
                if !atoms.is_auxiliary(v) && sat.lit_value(Lit::pos(v)) == LBool::True {
                    any_true = true;
                }
            }
            assert!(any_true, "no atom literal True after solve");
        } else {
            panic!("expected Lit");
        }
    }
}
