use super::*;

fn term(coeff: u32, vars: &[&str]) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(coeff),
        vars: vars.iter().map(|s| s.to_string()).collect(),
    }
}

#[test]
fn test_push_pop_basic() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    match solver.check() {
        SolveOutcome::Sat(_) => {}
        _ => panic!("expected SAT before push"),
    }
    solver.push();
    solver.assert_assignment("x", BigUint::from(3u32));
    match solver.check() {
        SolveOutcome::Unsat(_) => {}
        _ => panic!("expected UNSAT after adding contradiction"),
    }
    solver.pop();
    match solver.check() {
        SolveOutcome::Sat(m) => assert_eq!(m["x"], BigUint::from(2u32)),
        _ => panic!("expected SAT after pop"),
    }
}

#[test]
fn test_nested_push_pop() {
    let mut solver = IncrementalSolver::new(BigUint::from(11u32), false);
    // x + y - 7 = 0
    solver.assert_equality(vec![
        term(1, &["x"]),
        term(1, &["y"]),
        NamedTerm {
            coeff: BigUint::from(11u32 - 7),
            vars: vec![],
        },
    ]);
    solver.push();
    solver.assert_assignment("x", BigUint::from(3u32));
    solver.push();
    solver.assert_assignment("y", BigUint::from(4u32));
    match solver.check() {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(3u32));
            assert_eq!(m["y"], BigUint::from(4u32));
        }
        _ => panic!("expected SAT at depth 2"),
    }
    solver.pop();
    solver.assert_assignment("y", BigUint::from(5u32));
    match solver.check() {
        SolveOutcome::Unsat(_) => {}
        _ => panic!("expected UNSAT at depth 2 with y=5"),
    }
    solver.pop();
    assert_eq!(solver.push_depth(), 0);
    match solver.check() {
        SolveOutcome::Sat(_) => {}
        _ => panic!("expected SAT at depth 0"),
    }
}

#[test]
fn pop_without_push_is_noop() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    assert_eq!(solver.num_facts(), 1);
    solver.pop(); // no checkpoint pushed — facts retained.
    assert_eq!(solver.num_facts(), 1);
    assert_eq!(solver.push_depth(), 0);
}

#[test]
fn disequality_unsat_when_endpoints_equal_and_sat_otherwise() {
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    solver.assert_assignment("y", BigUint::from(2u32));
    solver.assert_disequality("x", "y");
    match solver.check() {
        SolveOutcome::Unsat(_) => {}
        other => panic!("expected UNSAT, got {:?}", other),
    }
    // Different witnesses: x=2, y=3 satisfies x≠y.
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    solver.assert_assignment("y", BigUint::from(3u32));
    solver.assert_disequality("x", "y");
    match solver.check() {
        SolveOutcome::Sat(m) => {
            assert_eq!(m["x"], BigUint::from(2u32));
            assert_eq!(m["y"], BigUint::from(3u32));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn equality_with_repeated_var_encodes_as_higher_exponent() {
    // x^2 = 4 in GF(7): vars=["x", "x"] should produce a quadratic.
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    // x^2 + (-4) = 0 (encoded as x^2 + 3 = 0 in GF(7)).
    solver.assert_equality(vec![
        term(1, &["x", "x"]),
        NamedTerm {
            coeff: BigUint::from(7u32 - 4),
            vars: vec![],
        },
    ]);
    match solver.check() {
        SolveOutcome::Sat(m) => {
            let x = m["x"].clone();
            let xx = (&x * &x) % BigUint::from(7u32);
            assert_eq!(xx, BigUint::from(4u32));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn check_with_timeout_eventually_returns() {
    // Trivial instance; just exercise the timeout-wrapper code path.
    let mut solver = IncrementalSolver::new(BigUint::from(7u32), false);
    solver.assert_assignment("x", BigUint::from(2u32));
    let outcome = solver.check_with_timeout(std::time::Duration::from_secs(5));
    assert!(matches!(outcome, SolveOutcome::Sat(_)));
}
