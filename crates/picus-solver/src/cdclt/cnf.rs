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
    lhs: &[crate::frontend::encoder::PolyTerm],
    rhs: &[crate::frontend::encoder::PolyTerm],
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
#[path = "cnf_tests.rs"]
mod tests;
