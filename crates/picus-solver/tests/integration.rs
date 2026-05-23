//! Integration test: complete solve pipeline.

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::{LegacyConstraintSystem, LegacyPolyTerm, encode};
use num_bigint::BigUint;
use num_traits::{One, Zero};

fn solve(system: &LegacyConstraintSystem) -> SolveOutcome {
    let encoded = encode(system).unwrap();
    solve_encoded(&encoded)
}

#[test]
fn test_is_zero_sound() {
    let p = BigUint::from(17u32);
    let system = LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["m".into(), "x".into()] },
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["iz".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["iz".into(), "x".into()] }],
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["mp".into(), "x".into()] },
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["izp".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["izp".into(), "x".into()] }],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match solve(&system) {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(m) => panic!("Expected UNSAT but got SAT: {:?}", m),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_is_zero_unsound() {
    let p = BigUint::from(17u32);
    let system = LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["m".into(), "x".into()] },
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["iz".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["mp".into(), "x".into()] },
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["izp".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match solve(&system) {
        SolveOutcome::Sat(model) => {
            assert_ne!(model.get("iz"), model.get("izp"), "iz ≠ izp: {:?}", model);
        }
        SolveOutcome::Unsat(_) => panic!("Expected SAT but got UNSAT"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_contradiction_unsat() {
    let p = BigUint::from(17u32);
    let system = LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["x".into()] },
                LegacyPolyTerm { coeff: BigUint::from(12u32), vars: vec![] },
            ],
        ],
        disequalities: vec![],
        assignments: vec![("x".into(), BigUint::from(3u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match solve(&system) {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(_) => panic!("Expected UNSAT"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_inverse_unique() {
    let p = BigUint::from(17u32);
    let system = LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["a".into(), "b".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["ap".into(), "bp".into()] },
                LegacyPolyTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
        ],
        disequalities: vec![("b".into(), "bp".into())],
        assignments: vec![
            ("a".into(), BigUint::from(2u32)),
            ("ap".into(), BigUint::from(2u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };
    match solve(&system) {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(_) => panic!("Expected UNSAT: inverse is unique"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_multiple_disequalities_sat() {
    // x*y = 1, x ≠ 0, y ≠ 0 over GF(7).  SAT (e.g., x=2, y=4).
    let p = BigUint::from(7u32);
    let system = LegacyConstraintSystem {
        prime: p,
        equalities: vec![
            vec![
                LegacyPolyTerm { coeff: BigUint::one(), vars: vec!["x".into(), "y".into()] },
                LegacyPolyTerm { coeff: BigUint::from(6u32), vars: vec![] }, // -1 mod 7
            ],
        ],
        disequalities: vec![
            ("x".into(), "zero".into()),
            ("y".into(), "zero".into()),
        ],
        assignments: vec![("zero".into(), BigUint::from(0u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = encode(&system).unwrap();
    let n_witnesses = encoded.poly_ring.var_names.iter().filter(|n| n.starts_with("__w_diseq_")).count();
    assert_eq!(n_witnesses, 2, "should create 2 Rabinowitsch witnesses");
    match solve_encoded(&encoded) {
        SolveOutcome::Sat(model) => {
            let xv = &model["x"];
            let yv = &model["y"];
            assert!(!xv.is_zero(), "x must be nonzero");
            assert!(!yv.is_zero(), "y must be nonzero");
            let prod = (xv * yv) % BigUint::from(7u32);
            assert_eq!(prod, BigUint::one());
        }
        SolveOutcome::Unsat(_) => panic!("expected SAT"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_multiple_disequalities_unsat() {
    // x = 0, x ≠ 0 (twice).  UNSAT.
    let p = BigUint::from(7u32);
    let system = LegacyConstraintSystem {
        prime: p,
        equalities: vec![],
        disequalities: vec![
            ("x".into(), "zero".into()),
            ("x".into(), "zero".into()),  // duplicate diseq, just to test 2 witnesses
        ],
        assignments: vec![
            ("x".into(), BigUint::from(0u32)),
            ("zero".into(), BigUint::from(0u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };
    match solve(&system) {
        SolveOutcome::Unsat(_) => {}
        _ => panic!("expected UNSAT"),
    }
}
