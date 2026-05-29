//! ZK-gadget semantics through `solve_encoded`: IsZero soundness vs.
//! unsoundness, field-inverse uniqueness, and disequality-witness
//! encoding (single and multiple `≠` constraints, SAT and UNSAT).

mod common;
use common::{NamedSystem, NamedTerm};

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_solver::core::{solve_encoded, SolveOutcome};

fn ipt(c: u64, vars: &[&str]) -> NamedTerm {
    NamedTerm {
        coeff: BigUint::from(c),
        vars: vars.iter().map(|s| s.to_string()).collect(),
    }
}

#[test]
fn test_is_zero_sound() {
    let p = BigUint::from(17u32);
    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["m".into(), "x".into()] },
                NamedTerm { coeff: BigUint::one(), vars: vec!["iz".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![NamedTerm { coeff: BigUint::one(), vars: vec!["iz".into(), "x".into()] }],
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["mp".into(), "x".into()] },
                NamedTerm { coeff: BigUint::one(), vars: vec!["izp".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![NamedTerm { coeff: BigUint::one(), vars: vec!["izp".into(), "x".into()] }],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match system.solve() {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(m) => panic!("Expected UNSAT but got SAT: {:?}", m),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_is_zero_unsound() {
    let p = BigUint::from(17u32);
    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["m".into(), "x".into()] },
                NamedTerm { coeff: BigUint::one(), vars: vec!["iz".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["mp".into(), "x".into()] },
                NamedTerm { coeff: BigUint::one(), vars: vec!["izp".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match system.solve() {
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
    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![vec![
            NamedTerm { coeff: BigUint::one(), vars: vec!["x".into()] },
            NamedTerm { coeff: BigUint::from(12u32), vars: vec![] },
        ]],
        disequalities: vec![],
        assignments: vec![("x".into(), BigUint::from(3u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    match system.solve() {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(_) => panic!("Expected UNSAT"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_inverse_unique() {
    let p = BigUint::from(17u32);
    let system = NamedSystem {
        prime: p.clone(),
        equalities: vec![
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["a".into(), "b".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
            ],
            vec![
                NamedTerm { coeff: BigUint::one(), vars: vec!["ap".into(), "bp".into()] },
                NamedTerm { coeff: BigUint::from(16u32), vars: vec![] },
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
    match system.solve() {
        SolveOutcome::Unsat(_) => {}
        SolveOutcome::Sat(_) => panic!("Expected UNSAT: inverse is unique"),
        _ => panic!("unexpected outcome"),
    }
}

#[test]
fn test_multiple_disequalities_sat() {
    let p = BigUint::from(7u32);
    let system = NamedSystem {
        prime: p,
        equalities: vec![vec![
            NamedTerm { coeff: BigUint::one(), vars: vec!["x".into(), "y".into()] },
            NamedTerm { coeff: BigUint::from(6u32), vars: vec![] },
        ]],
        disequalities: vec![
            ("x".into(), "zero".into()),
            ("y".into(), "zero".into()),
        ],
        assignments: vec![("zero".into(), BigUint::from(0u32))],
        add_field_polys: false,
        bitsums: vec![],
    };
    let encoded = system.encode().unwrap();
    let n_witnesses = encoded
        .poly_ring
        .var_names()
        .iter()
        .filter(|n| n.starts_with("__w_diseq_"))
        .count();
    assert_eq!(n_witnesses, 2);
    match solve_encoded(&encoded) {
        SolveOutcome::Sat(model) => {
            let xv = &model["x"];
            let yv = &model["y"];
            assert!(!xv.is_zero());
            assert!(!yv.is_zero());
            let prod = (xv * yv) % BigUint::from(7u32);
            assert_eq!(prod, BigUint::one());
        }
        SolveOutcome::Unsat(_) => panic!("expected SAT"),
        _ => panic!("unexpected outcome"),
    }
    let _ = ipt;
}

#[test]
fn test_multiple_disequalities_unsat() {
    let p = BigUint::from(7u32);
    let system = NamedSystem {
        prime: p,
        equalities: vec![],
        disequalities: vec![
            ("x".into(), "zero".into()),
            ("x".into(), "zero".into()),
        ],
        assignments: vec![
            ("x".into(), BigUint::from(0u32)),
            ("zero".into(), BigUint::from(0u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };
    match system.solve() {
        SolveOutcome::Unsat(_) => {}
        _ => panic!("expected UNSAT"),
    }
}
