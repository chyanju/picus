//! Criterion benchmarks for picus-solver.
//!
//! Measures end-to-end and per-phase performance across representative workloads:
//!
//! 1. **encode** — `LegacyConstraintSystem` → `EncodedSystem` (field/ring construction +
//!    polynomial building).
//! 2. **split_gb** — Groebner basis computation on the encoded system.
//! 3. **find_roots** — Univariate root finding via Cantor-Zassenhaus.
//! 4. **end-to-end** — Full `encode` + `solve_encoded` pipeline.
//!
//! Workloads:
//!   - `issue10937_gf7`    : 11-variable MAC linearity, GF(7) — the benchmark that
//!                           revealed the 600,000x performance bug.
//!   - `bigff_is_zero_gf_bn128` : 4-variable soundness proof over BN128 (large prime).
//!   - `field_poly_gf7`    : Fermat's little theorem a^7 = a, with field polys.
//!   - `random_6var_gf11`  : Random 6-variable system (SAT by construction).
//!   - `find_roots_gf7`    : Univariate root finding over GF(7).
//!   - `find_roots_big`    : Univariate root finding over 2^255-19.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use num_bigint::BigUint;
use num_traits::One;

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::{LegacyConstraintSystem, LegacyPolyTerm, encode};
use picus_solver::field::FfField;
use picus_solver::roots::find_roots;

// ── Helpers ──────────────────────────────────────────────────────────────────

fn ct(c: u64) -> LegacyPolyTerm { LegacyPolyTerm { coeff: BigUint::from(c), vars: vec![] } }
fn ctb(c: BigUint) -> LegacyPolyTerm { LegacyPolyTerm { coeff: c, vars: vec![] } }
fn vt(v: &str) -> LegacyPolyTerm { LegacyPolyTerm { coeff: BigUint::one(), vars: vec![v.into()] } }
fn svt(c: u64, v: &str) -> LegacyPolyTerm { LegacyPolyTerm { coeff: BigUint::from(c), vars: vec![v.into()] } }
fn pt(c: u64, vars: &[&str]) -> LegacyPolyTerm {
    LegacyPolyTerm { coeff: BigUint::from(c), vars: vars.iter().map(|s| s.to_string()).collect() }
}

// ── Workload builders ───────────────────────────────────────────────────────

fn issue10937_system() -> LegacyConstraintSystem {
    let p = BigUint::from(7u32);
    let p_minus_1: BigUint = &p - BigUint::one();
    let mut system = LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![vt("mac1"), svt(6, "k1"), pt(6, &["d", "m1"])],
            vec![vt("mac2"), svt(6, "k2"), pt(6, &["d", "m2"])],
            vec![vt("dm"), pt(6, &["d", "m1"]), pt(6, &["d", "m2"])],
            vec![vt("s"), svt(6, "k1"), svt(6, "k2"), svt(6, "dm")],
        ],
        disequalities: vec![("mac_sum".into(), "s".into())],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    };
    system.equalities.push(vec![
        vt("mac_sum"),
        svt(p_minus_1.to_u64_digits()[0], "mac1"),
        svt(p_minus_1.to_u64_digits()[0], "mac2"),
    ]);
    system
}

fn bigff_is_zero_system() -> LegacyConstraintSystem {
    let p: BigUint = "21888242871839275222246405745257275088548364400416034343698204186575808495617"
        .parse().unwrap();
    let p_minus_1 = &p - BigUint::one();
    LegacyConstraintSystem {
        prime: p.clone(),
        equalities: vec![
            vec![pt(1, &["m", "x"]), vt("iz"), ctb(p_minus_1.clone())],
            vec![pt(1, &["iz", "x"])],
            vec![
                pt(1, &["iz", "iz", "w"]),
                LegacyPolyTerm { coeff: p_minus_1.clone(), vars: vec!["iz".into(), "w".into()] },
                ctb(p_minus_1.clone()),
            ],
        ],
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    }
}

fn field_poly_gf7_system() -> LegacyConstraintSystem {
    LegacyConstraintSystem {
        prime: BigUint::from(7u32),
        equalities: vec![
            vec![vt("a2"), pt(6, &["a", "a"])],
            vec![vt("a4"), pt(6, &["a2", "a2"])],
            vec![vt("a6"), pt(6, &["a4", "a2"])],
            vec![vt("a7"), pt(6, &["a6", "a"])],
        ],
        disequalities: vec![("a7".into(), "a".into())],
        assignments: vec![],
        add_field_polys: true,
        bitsums: vec![],
    }
}

fn random_6var_system() -> LegacyConstraintSystem {
    // 9 random linear constraints over GF(11) that are SAT (planted root: all zeros).
    // Each eq: c_0*x_0 + c_1*x_1 + ... + c_5*x_5 = 0 (trivially satisfied by the zero point).
    let coeffs: Vec<Vec<u64>> = vec![
        vec![3, 7, 1, 0, 5, 2],
        vec![0, 4, 8, 1, 0, 10],
        vec![1, 0, 0, 6, 3, 0],
        vec![0, 0, 9, 0, 7, 1],
        vec![5, 2, 0, 3, 0, 0],
        vec![0, 1, 4, 0, 0, 8],
        vec![7, 0, 0, 0, 2, 5],
        vec![0, 3, 0, 9, 0, 1],
        vec![2, 0, 6, 0, 1, 0],
    ];
    let vars = ["x0", "x1", "x2", "x3", "x4", "x5"];
    let equalities: Vec<Vec<LegacyPolyTerm>> = coeffs.iter().map(|row| {
        row.iter().enumerate()
            .filter(|&(_, c)| *c != 0)
            .map(|(i, c)| svt(*c, vars[i]))
            .collect()
    }).collect();
    LegacyConstraintSystem {
        prime: BigUint::from(11u32),
        equalities,
        disequalities: vec![],
        assignments: vec![],
        add_field_polys: false,
        bitsums: vec![],
    }
}

// ── Benchmarks ──────────────────────────────────────────────────────────────

fn bench_encode(c: &mut Criterion) {
    let mut group = c.benchmark_group("encode");

    let systems: Vec<(&str, LegacyConstraintSystem)> = vec![
        ("issue10937_gf7", issue10937_system()),
        ("bigff_is_zero_bn128", bigff_is_zero_system()),
        ("field_poly_gf7", field_poly_gf7_system()),
        ("random_6var_gf11", random_6var_system()),
    ];

    for (name, sys) in &systems {
        group.bench_with_input(BenchmarkId::new("encode", name), sys, |b, sys| {
            b.iter(|| encode(black_box(sys)).unwrap());
        });
    }
    group.finish();
}

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("end_to_end");

    let systems: Vec<(&str, LegacyConstraintSystem)> = vec![
        ("issue10937_gf7", issue10937_system()),
        ("bigff_is_zero_bn128", bigff_is_zero_system()),
        ("field_poly_gf7", field_poly_gf7_system()),
        ("random_6var_gf11", random_6var_system()),
    ];

    for (name, sys) in &systems {
        group.bench_with_input(BenchmarkId::new("solve", name), sys, |b, sys| {
            b.iter(|| {
                let encoded = encode(black_box(sys)).unwrap();
                solve_encoded(&encoded)
            });
        });
    }
    group.finish();
}

fn bench_find_roots(c: &mut Criterion) {
    let mut group = c.benchmark_group("find_roots");

    // GF(7): x^4 - x^3 (roots 0, 1)
    {
        let ff = FfField::new(BigUint::from(7u32));
        let mut coeffs = vec![ff.zero(); 5];
        coeffs[3] = ff.from_biguint(&BigUint::from(6u32));
        coeffs[4] = ff.one();
        group.bench_function("degree4_gf7", |b| {
            b.iter(|| find_roots(black_box(&ff), black_box(&coeffs)));
        });
    }

    // 2^255-19: x^2 - x + 1
    {
        let p: BigUint = "57896044618658097711785492504343953926634992332820282019728792003956564819949"
            .parse().unwrap();
        let ff = FfField::new(p.clone());
        let pm1 = &p - BigUint::one();
        let mut coeffs = vec![ff.zero(); 3];
        coeffs[0] = ff.one();
        coeffs[1] = ff.from_biguint(&pm1);
        coeffs[2] = ff.one();
        group.bench_function("degree2_curve25519", |b| {
            b.iter(|| find_roots(black_box(&ff), black_box(&coeffs)));
        });
    }

    group.finish();
}

criterion_group!(benches, bench_encode, bench_end_to_end, bench_find_roots);
criterion_main!(benches);
