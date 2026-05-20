//! Performance benchmarks for picus-solver.
//! Run with: cargo test -p picus-solver --test bench_perf --release -- --ignored --nocapture

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::{encode, encode_no_auto_bitsum, ConstraintSystem, PolyTerm};
use picus_solver::gb::{compute_gb, GbResult};
use num_bigint::BigUint;
use num_traits::One;
use std::time::Instant;

fn pterm(coeff: u64, vars: &[&str]) -> PolyTerm {
    PolyTerm { coeff: BigUint::from(coeff), vars: vars.iter().map(|s| s.to_string()).collect() }
}

fn bn128_prime() -> BigUint {
    "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse()
        .unwrap()
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

/// Build a k-bit decomposition system over BN128:
///   - K bit constraints `b_i*(b_i - 1) = 0`
///   - one bitsum equality `b_0 + 2*b_1 + ... + 2^{K-1}*b_{K-1} - target = 0`
fn bitdecomp_bn128_system(k: usize, target: u64) -> ConstraintSystem {
    let p = bn128_prime();
    let pm1 = &p - BigUint::one();
    let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
    for i in 0..k {
        let bi = format!("b{}", i);
        equalities.push(vec![
            PolyTerm { coeff: BigUint::one(), vars: vec![bi.clone(), bi.clone()] },
            PolyTerm { coeff: pm1.clone(), vars: vec![bi] },
        ]);
    }
    let mut sum: Vec<PolyTerm> = Vec::with_capacity(k + 1);
    let mut coeff = BigUint::one();
    let two = BigUint::from(2u32);
    for i in 0..k {
        sum.push(PolyTerm { coeff: coeff.clone(), vars: vec![format!("b{}", i)] });
        coeff = (&coeff * &two) % &p;
    }
    sum.push(PolyTerm { coeff: &p - BigUint::from(target), vars: vec![] });
    equalities.push(sum);
    ConstraintSystem {
        prime: p,
        equalities,
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    }
}

fn time_solve_median(cs: &ConstraintSystem, iters: usize, use_auto: bool) -> (u128, &'static str) {
    let mut total_times: Vec<u128> = Vec::with_capacity(iters);
    let mut verdict = "unknown";
    for _ in 0..iters {
        let t = Instant::now();
        let enc = if use_auto {
            encode(cs).unwrap()
        } else {
            encode_no_auto_bitsum(cs).unwrap()
        };
        let out = solve_encoded(&enc);
        total_times.push(t.elapsed().as_micros());
        verdict = match out {
            SolveOutcome::Sat(_) => "sat",
            SolveOutcome::Unsat(_) => "unsat",
            SolveOutcome::Unknown => "unknown",
        };
    }
    total_times.sort();
    (total_times[iters / 2], verdict)
}

/// Bitdecomp speedup from `auto_extract_bitsums`: compare `encode`
/// (auto-extract on) against `encode_no_auto_bitsum` across K∈{6,8,10,12}.
/// Verdicts must agree; only timing differs.
#[test]
#[ignore]
fn bench_bitdecomp_auto_extract_speedup() {
    let iters = 3;
    println!(
        "{:>3} | {:>12} | {:<7} | {:>14} | {:>14} | speedup",
        "K", "target", "verdict", "no_auto_us", "auto_us"
    );
    println!("{}", "-".repeat(78));
    for &k in &[6usize, 8, 10, 12] {
        let target = if k < 64 { (1u64 << k) - 3 } else { (1u64 << 32) - 3 };
        let cs = bitdecomp_bn128_system(k, target);

        // For K >= 10 the no-auto path can blow up; cap to 1 iter.
        let no_auto_iters = if k >= 10 { 1 } else { iters };
        let (t_no_auto, v_no_auto) = time_solve_median(&cs, no_auto_iters, false);
        let (t_auto, v_auto) = time_solve_median(&cs, iters, true);

        assert_eq!(v_no_auto, v_auto, "verdict disagreement at K={}", k);

        let speedup = if t_auto == 0 {
            "inf".to_string()
        } else {
            format!("{:.1}x", t_no_auto as f64 / t_auto as f64)
        };
        println!(
            "{:>3} | {:>12} | {:<7} | {:>14} | {:>14} | {}",
            k, target, v_auto, t_no_auto, t_auto, speedup
        );
    }
}
