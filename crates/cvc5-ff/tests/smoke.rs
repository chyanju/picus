//! End-to-end smoke test exercising the FFI wrapper through a minimal
//! finite-field query. Verifies that the cvc5-ff bindings link, that
//! the term manager and solver constructors round-trip, and that
//! `check_sat` produces sane `is_sat` / `is_unsat` discrimination.

use cvc5_ff::{Kind, Solver, TermManager};

#[test]
fn qf_ff_sat_then_unsat() {
    // x = 1 over GF(7) is SAT.
    let tm = TermManager::new();
    let mut solver = Solver::new(&tm);
    solver.set_logic("QF_FF");
    let ff = tm.mk_ff_sort("7", 10);
    let x = tm.mk_const(ff.clone(), "x");
    let one = tm.mk_ff_elem("1", ff.clone(), 10);
    solver.assert_formula(tm.mk_term(Kind::Equal, &[x.clone(), one]));
    assert!(solver.check_sat().is_sat());

    // Tighten with x = 2 to force UNSAT (in a fresh solver).
    let mut solver2 = Solver::new(&tm);
    solver2.set_logic("QF_FF");
    let x2 = tm.mk_const(ff.clone(), "x");
    let one2 = tm.mk_ff_elem("1", ff.clone(), 10);
    let two = tm.mk_ff_elem("2", ff.clone(), 10);
    solver2.assert_formula(tm.mk_term(Kind::Equal, &[x2.clone(), one2]));
    solver2.assert_formula(tm.mk_term(Kind::Equal, &[x2, two]));
    assert!(solver2.check_sat().is_unsat());
}
