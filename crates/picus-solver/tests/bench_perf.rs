//! Performance benchmarks for picus-solver.
//! Run with: cargo +nightly test -p picus-solver --test bench_perf -- --ignored

use picus_solver::encoder::{ConstraintSystem, PolyTerm, encode};
use picus_solver::gb::{compute_gb, GbResult};
use num_bigint::BigUint;
use num_traits::One;
use std::time::Instant;

fn pterm(coeff: u64, vars: &[&str]) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(coeff), vars: vars.iter().map(|s| s.to_string()).collect() }
}

/// Benchmark: IsZero uniqueness over BN128 field
#[test]
#[ignore] // run manually with --ignored
fn bench_is_zero_bn128() {
    let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617".parse().unwrap();
    let pm1 = &p - BigUint::one();

    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pterm(1, &["m", "x"]), pterm(1, &["iz"]), PolyTerm { coeff: pm1.clone(), vars: vec![] }],
            vec![pterm(1, &["iz", "x"])],
            vec![pterm(1, &["mp", "x"]), pterm(1, &["izp"]), PolyTerm { coeff: pm1.clone(), vars: vec![] }],
            vec![pterm(1, &["izp", "x"])],
        ],
        disequalities: vec![("iz".into(), "izp".into())],
        assignments: vec![("x".into(), BigUint::from(5u32))],
        add_field_polys: false,
        bitsums: vec![],
    };

    let start = Instant::now();
    let encoded = encode(&system).unwrap();
    let encode_time = start.elapsed();

    let start = Instant::now();
    let result = compute_gb(&encoded.poly_ring, encoded.polynomials);
    let gb_time = start.elapsed();

    println!("BN128 IsZero uniqueness:");
    println!("  Encoding: {:?}", encode_time);
    println!("  GB computation: {:?}", gb_time);
    println!("  Total: {:?}", encode_time + gb_time);
    println!("  Result: {}", match result {
        GbResult::Trivial => "UNSAT",
        GbResult::NonTrivial(_) => "SAT/UNKNOWN",
        GbResult::Timeout => "TIMEOUT",
    });
}

/// Benchmark: Multiple constraints over GF(17)
#[test]
#[ignore]
fn bench_multi_constraint_gf17() {
    let p = BigUint::from(17u32);

    // 5 binary constraints + sum constraint
    let system = ConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pterm(1, &["b0", "b0"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b0".into()] }],
            vec![pterm(1, &["b1", "b1"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b1".into()] }],
            vec![pterm(1, &["b2", "b2"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b2".into()] }],
            vec![pterm(1, &["b3", "b3"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b3".into()] }],
            // s = b0 + 2*b1 + 4*b2 + 8*b3
            vec![
                PolyTerm { coeff: BigUint::one(), vars: vec!["s".into()] },
                PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b0".into()] },
                PolyTerm { coeff: BigUint::from(15u32), vars: vec!["b1".into()] },
                PolyTerm { coeff: BigUint::from(13u32), vars: vec!["b2".into()] },
                PolyTerm { coeff: BigUint::from(9u32), vars: vec!["b3".into()] },
            ],
            // same for alt
            vec![pterm(1, &["b0p", "b0p"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b0p".into()] }],
            vec![pterm(1, &["b1p", "b1p"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b1p".into()] }],
            vec![pterm(1, &["b2p", "b2p"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b2p".into()] }],
            vec![pterm(1, &["b3p", "b3p"]), PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b3p".into()] }],
            vec![
                PolyTerm { coeff: BigUint::one(), vars: vec!["sp".into()] },
                PolyTerm { coeff: BigUint::from(16u32), vars: vec!["b0p".into()] },
                PolyTerm { coeff: BigUint::from(15u32), vars: vec!["b1p".into()] },
                PolyTerm { coeff: BigUint::from(13u32), vars: vec!["b2p".into()] },
                PolyTerm { coeff: BigUint::from(9u32), vars: vec!["b3p".into()] },
            ],
        ],
        disequalities: vec![("s".into(), "sp".into())],
        assignments: vec![
            ("b0".into(), BigUint::one()),
            ("b1".into(), BigUint::from(0u32)),
            ("b2".into(), BigUint::one()),
            ("b3".into(), BigUint::from(0u32)),
            ("b0p".into(), BigUint::one()),
            ("b1p".into(), BigUint::from(0u32)),
            ("b2p".into(), BigUint::one()),
            ("b3p".into(), BigUint::from(0u32)),
        ],
        add_field_polys: false,
        bitsums: vec![],
    };

    let start = Instant::now();
    let encoded = encode(&system).unwrap();
    let result = compute_gb(&encoded.poly_ring, encoded.polynomials);
    let total = start.elapsed();

    println!("GF(17) bit decomposition uniqueness:");
    println!("  Total: {:?}", total);
    println!("  Result: {}", match result {
        GbResult::Trivial => "UNSAT",
        GbResult::NonTrivial(_) => "SAT/UNKNOWN",
        GbResult::Timeout => "TIMEOUT",
    });
}
