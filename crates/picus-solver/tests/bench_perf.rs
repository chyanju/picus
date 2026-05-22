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

/// F4 vs per-pair on workloads sized to expose F4's amortisation
/// benefit: larger ideals, more variables, and the cyclic-N family
/// (a standard GB benchmark that produces many same-sugar S-pair
/// batches).
///
/// Run manually:
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   bench_f4_vs_per_pair_large -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_vs_per_pair_large() {
    use picus_solver::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use picus_solver::ff::monomial::MonomialOrder;
    use picus_solver::ff::polynomial::PolyRing;
    use picus_solver::ff::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    /// `cyclic-N`: the N-variable cyclic ideal. Classical GB benchmark
    /// known to produce many same-sugar batches and a large basis.
    fn cyclic_n(n: usize, ring: &Arc<PolyRing>) -> Vec<picus_solver::ff::polynomial::Polynomial> {
        use picus_solver::ff::polynomial::Polynomial;
        let xs: Vec<Polynomial> = (0..n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys: Vec<Polynomial> = Vec::new();
        // f_d = sum over rotation r of (product x_{(r+0)..r+d})  for d = 1..n
        for d in 1..n {
            let mut acc = Polynomial::zero();
            for r in 0..n {
                let mut prod = xs[r % n].clone();
                for k in 1..d {
                    prod = prod.mul(&xs[(r + k) % n], ring);
                }
                acc = acc.add(&prod, ring);
            }
            polys.push(acc);
        }
        // f_n = x_0 * x_1 * ... * x_{n-1} - 1
        let mut p = xs[0].clone();
        for k in 1..n {
            p = p.mul(&xs[k], ring);
        }
        let one = ring.field.one();
        p = p.sub(&Polynomial::constant(one, ring), ring);
        polys.push(p);
        polys
    }

    fn run_one(
        polys: &[picus_solver::ff::polynomial::Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
    ) -> u128 {
        let cfg = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: false,
            use_f4,
        };
        let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
        let t = Instant::now();
        igb.add_generators(polys.to_vec())
            .expect("add_generators");
        t.elapsed().as_micros()
    }

    println!();
    println!(
        "{:<18} | {:>8} | {:>10} | {:>10} | {}",
        "workload", "n_polys", "pp_us", "f4_us", "f4/pp"
    );
    println!("{}", "-".repeat(70));

    let primes_and_orders: Vec<(BigUint, usize)> = vec![
        (BigUint::from(7919u32), 4), // cyclic-4
        (BigUint::from(7919u32), 5), // cyclic-5 (heavier)
        (BigUint::from(7919u32), 6), // cyclic-6 (more same-sugar batches)
    ];

    for (prime, n_vars) in &primes_and_orders {
        let names: Vec<String> = (0..*n_vars).map(|i| format!("x{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = cyclic_n(*n_vars, &ring);
        // Warm-up + 3 iterations, take median.
        let _ = run_one(&polys, &ring, false);
        let mut pp_times = Vec::new();
        for _ in 0..3 {
            pp_times.push(run_one(&polys, &ring, false));
        }
        pp_times.sort();
        let _ = run_one(&polys, &ring, true);
        let mut f4_times = Vec::new();
        for _ in 0..3 {
            f4_times.push(run_one(&polys, &ring, true));
        }
        f4_times.sort();
        let pp_med = pp_times[1];
        let f4_med = f4_times[1];
        let ratio = if pp_med == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4_med as f64 / pp_med as f64)
        };
        println!(
            "{:<18} | {:>8} | {:>10} | {:>10} | {}",
            format!("cyclic-{}", n_vars),
            polys.len(),
            pp_med,
            f4_med,
            ratio
        );
    }

    // Dense random ideals: large basis, many overlapping monomials.
    {
        let prime = BigUint::from(7919u32);
        let n_vars = 4usize;
        let names: Vec<String> = (0..n_vars).map(|i| format!("x{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime),
            names,
            MonomialOrder::DegRevLex,
        );
        let mut seed = 42u64;
        let mut rand = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed
        };
        for &n_polys in &[10usize, 20, 30] {
            let mut polys = Vec::new();
            for _ in 0..n_polys {
                let mut acc = picus_solver::ff::polynomial::Polynomial::zero();
                for _ in 0..6 {
                    let coeff = ((rand() % 7000) + 1) as i64;
                    let c = ring.field.from_int(coeff);
                    let i = (rand() as usize) % n_vars;
                    let j = (rand() as usize) % n_vars;
                    let xi = picus_solver::ff::polynomial::Polynomial::variable(i, &ring);
                    let xj = picus_solver::ff::polynomial::Polynomial::variable(j, &ring);
                    let term = xi.mul(&xj, &ring);
                    let scaled = term.mul(
                        &picus_solver::ff::polynomial::Polynomial::constant(c, &ring),
                        &ring,
                    );
                    acc = acc.add(&scaled, &ring);
                }
                let cc = ring.field.from_int(((rand() % 7) + 1) as i64);
                let cp = picus_solver::ff::polynomial::Polynomial::constant(cc, &ring);
                acc = acc.add(&cp, &ring);
                if !acc.is_zero() {
                    polys.push(acc);
                }
            }
            let _ = run_one(&polys, &ring, false);
            let mut pp_times = Vec::new();
            for _ in 0..3 {
                pp_times.push(run_one(&polys, &ring, false));
            }
            pp_times.sort();
            let _ = run_one(&polys, &ring, true);
            let mut f4_times = Vec::new();
            for _ in 0..3 {
                f4_times.push(run_one(&polys, &ring, true));
            }
            f4_times.sort();
            let pp_med = pp_times[1];
            let f4_med = f4_times[1];
            let ratio = if pp_med == 0 {
                "inf".to_string()
            } else {
                format!("{:.2}x", f4_med as f64 / pp_med as f64)
            };
            println!(
                "{:<18} | {:>8} | {:>10} | {:>10} | {}",
                format!("dense-{}-{}vars", n_polys, n_vars),
                polys.len(),
                pp_med,
                f4_med,
                ratio
            );
        }
    }
}

/// F4-vs-per-pair bench on non-cyclic GB families: Katsura-3,
/// Katsura-4, and a 4-variable ideal whose S-pair LCMs share
/// substructure. Coverage for the medium-batch regime that the
/// cyclic-N corpus does not exercise.
///
/// Run with `PICUS_GB_STATS=1` to print per-run F4 batch counters:
///
/// ```bash
/// PICUS_USE_F4=1 PICUS_GB_STATS=1 cargo test -p picus-solver \
///   --test bench_perf --release \
///   bench_f4_non_cyclic_workloads -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_non_cyclic_workloads() {
    use picus_solver::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use picus_solver::ff::monomial::MonomialOrder;
    use picus_solver::ff::polynomial::{PolyRing, Polynomial};
    use picus_solver::ff::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    /// Katsura(n) in `n+1` variables `u_0, …, u_n` (degrevlex):
    /// ```text
    ///   P_i = Σ_{j=-n..n} u_{|j|} · u_{|i-j|} - u_i   for 0 ≤ i ≤ n-1
    ///   P_n = Σ_{j=-n..n} u_{|j|} - 1
    /// ```
    fn katsura_n(n: usize, ring: &Arc<PolyRing>) -> Vec<Polynomial> {
        let xs: Vec<Polynomial> = (0..=n).map(|i| Polynomial::variable(i, ring)).collect();
        let mut polys: Vec<Polynomial> = Vec::new();
        let two = ring.field.from_int(2);
        let two_poly = Polynomial::constant(two.clone(), ring);
        for i in 0..n {
            let mut acc = Polynomial::zero();
            for j in -(n as i32)..=(n as i32) {
                let aj = (j.unsigned_abs()) as usize;
                let ak = ((i as i32 - j).unsigned_abs()) as usize;
                if aj > n || ak > n {
                    continue;
                }
                let prod = xs[aj].mul(&xs[ak], ring);
                acc = acc.add(&prod, ring);
            }
            acc = acc.sub(&xs[i], ring);
            polys.push(acc);
        }
        // P_n: u_0 + 2·u_1 + 2·u_2 + … + 2·u_n - 1
        let mut tail = xs[0].clone();
        for k in 1..=n {
            let scaled = xs[k].mul(&two_poly, ring);
            tail = tail.add(&scaled, ring);
        }
        let one = ring.field.one();
        tail = tail.sub(&Polynomial::constant(one, ring), ring);
        polys.push(tail);
        polys
    }

    /// 4-variable degree-2/4 ideal whose S-pair LCMs cluster inside
    /// a single sugar batch. LTs `(x·y, x·z, y·z, w·x, w·y, w·z,
    /// w·x·y·z)` give `lcm(f_1, f_2) = lcm(f_1, f_3) = lcm(f_2, f_3)
    /// = x·y·z` (three pairs sharing a degree-3 LCM) plus the
    /// symmetric block on `(w, x, y, z)`.
    fn diffuse_ideal(ring: &Arc<PolyRing>) -> Vec<Polynomial> {
        let w = Polynomial::variable(0, ring);
        let x = Polynomial::variable(1, ring);
        let y = Polynomial::variable(2, ring);
        let z = Polynomial::variable(3, ring);
        let one = ring.field.one();
        let const_one = Polynomial::constant(one.clone(), ring);
        let f1 = x.mul(&y, ring).sub(&z, ring);
        let f2 = x.mul(&z, ring).sub(&y, ring);
        let f3 = y.mul(&z, ring).sub(&x, ring);
        let f4 = w.mul(&x, ring).sub(&const_one, ring);
        let f5 = w.mul(&y, ring).sub(&z, ring);
        let f6 = w.mul(&z, ring).sub(&y, ring);
        let f7 = w.mul(&x, ring).mul(&y, ring).mul(&z, ring).sub(&const_one, ring);
        vec![f1, f2, f3, f4, f5, f6, f7]
    }

    fn run_one(
        polys: &[Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
    ) -> u128 {
        let cfg = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: false,
            use_f4,
        };
        let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
        let t = Instant::now();
        igb.add_generators(polys.to_vec()).expect("add_generators");
        t.elapsed().as_micros()
    }

    fn median_times(polys: &[Polynomial], ring: &Arc<PolyRing>, use_f4: bool) -> u128 {
        // Warm-up + 3 measured runs; report the median.
        let _ = run_one(polys, ring, use_f4);
        let mut ts = Vec::new();
        for _ in 0..3 {
            ts.push(run_one(polys, ring, use_f4));
        }
        ts.sort();
        ts[1]
    }

    println!();
    println!(
        "{:<24} | {:>8} | {:>10} | {:>10} | {}",
        "workload", "n_polys", "pp_us", "f4_us", "f4/pp"
    );
    println!("{}", "-".repeat(76));

    let prime = BigUint::from(7919u32);

    // Katsura-3, Katsura-4. Average batch sizes straddle
    // `F4_MIN_BATCH = 12`.
    for n in [3usize, 4] {
        let names: Vec<String> = (0..=n).map(|i| format!("u{}", i)).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = katsura_n(n, &ring);
        let pp = median_times(&polys, &ring, false);
        let f4 = median_times(&polys, &ring, true);
        let ratio = if pp == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4 as f64 / pp as f64)
        };
        println!(
            "{:<24} | {:>8} | {:>10} | {:>10} | {}",
            format!("katsura-{}", n),
            polys.len(),
            pp,
            f4,
            ratio,
        );
    }

    // 4-variable ideal whose S-pair LCMs share substructure across
    // pairs (subject to coprime / GM / B pruning).
    {
        let names: Vec<String> = ["w", "x", "y", "z"].iter().map(|s| s.to_string()).collect();
        let ring = PolyRing::new(
            PrimeField::new(prime.clone()),
            names,
            MonomialOrder::DegRevLex,
        );
        let polys = diffuse_ideal(&ring);
        let pp = median_times(&polys, &ring, false);
        let f4 = median_times(&polys, &ring, true);
        let ratio = if pp == 0 {
            "inf".to_string()
        } else {
            format!("{:.2}x", f4 as f64 / pp as f64)
        };
        println!(
            "{:<24} | {:>8} | {:>10} | {:>10} | {}",
            "diffuse-4vars",
            polys.len(),
            pp,
            f4,
            ratio,
        );
    }
}

/// F4 vs per-pair geobucket: run the same workloads on both engines
/// in-process (via `IncrementalGB` with different `BuchbergerConfig`s)
/// and report median timings. Reads the default from `PICUS_USE_F4`
/// but overrides per-config; the env var is ignored here.
///
/// Run manually:
/// ```bash
/// cargo test -p picus-solver --test bench_perf --release \
///   bench_f4_vs_per_pair -- --ignored --nocapture
/// ```
#[test]
#[ignore]
fn bench_f4_vs_per_pair() {
    use picus_solver::ff::buchberger::{BuchbergerConfig, IncrementalGB};
    use picus_solver::ff::monomial::MonomialOrder;
    use picus_solver::ff::polynomial::PolyRing;
    use picus_solver::ff::field::PrimeField;
    use std::sync::Arc;
    use std::time::Instant;

    /// Build a synthetic ideal of size `n_polys` over `n_vars`
    /// variables in F_p, degree ≤ 2. Deterministic via `seed`.
    fn build_system(
        n_vars: usize,
        n_polys: usize,
        seed: u64,
        ring: &Arc<PolyRing>,
    ) -> Vec<picus_solver::ff::polynomial::Polynomial> {
        let mut s = seed;
        let mut rand = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        let mut out = Vec::new();
        for _ in 0..n_polys {
            let mut acc = picus_solver::ff::polynomial::Polynomial::zero();
            for _ in 0..6 {
                let coeff = ((rand() % 7000) + 1) as i64;
                let c = ring.field.from_int(coeff);
                let i = (rand() as usize) % n_vars;
                let j = (rand() as usize) % n_vars;
                let xi = picus_solver::ff::polynomial::Polynomial::variable(i, ring);
                let xj = picus_solver::ff::polynomial::Polynomial::variable(j, ring);
                let term = xi.mul(&xj, ring);
                let scaled = term.mul(
                    &picus_solver::ff::polynomial::Polynomial::constant(c, ring),
                    ring,
                );
                acc = acc.add(&scaled, ring);
            }
            let cc = ring.field.from_int(((rand() % 7) + 1) as i64);
            let cp = picus_solver::ff::polynomial::Polynomial::constant(cc, ring);
            acc = acc.add(&cp, ring);
            if !acc.is_zero() {
                out.push(acc);
            }
        }
        out
    }

    fn time_one(
        polys: &[picus_solver::ff::polynomial::Polynomial],
        ring: &Arc<PolyRing>,
        use_f4: bool,
        iters: usize,
    ) -> (u128, bool) {
        let mut times = Vec::with_capacity(iters);
        let mut trivial = false;
        for _ in 0..iters {
            let cfg = BuchbergerConfig {
                order: MonomialOrder::DegRevLex,
                cancel_token: None,
                abort_on_trivial: false,
                use_f4,
            };
            let mut igb = IncrementalGB::new(Arc::clone(ring), cfg);
            let t = Instant::now();
            trivial = igb
                .add_generators(polys.to_vec())
                .expect("add_generators");
            times.push(t.elapsed().as_micros());
        }
        times.sort();
        (times[iters / 2], trivial)
    }

    let prime = BigUint::from(7919u32); // first prime > 7000
    let names = vec!["x".into(), "y".into(), "z".into(), "w".into()];
    let ring = PolyRing::new(PrimeField::new(prime), names, MonomialOrder::DegRevLex);

    println!();
    println!(
        "{:<10} | {:>6} | {:>10} | {:>10} | {:>10} | {}",
        "n_polys", "seed", "pp_us", "f4_us", "f4/pp", "verdict"
    );
    println!("{}", "-".repeat(72));

    for n_polys in &[3usize, 5, 8, 12] {
        for seed in 1..=3u64 {
            let polys = build_system(4, *n_polys, seed, &ring);
            if polys.is_empty() {
                continue;
            }
            let iters = 5;
            let (pp_med, pp_trivial) = time_one(&polys, &ring, false, iters);
            let (f4_med, f4_trivial) = time_one(&polys, &ring, true, iters);
            assert_eq!(pp_trivial, f4_trivial,
                "verdict disagreement n_polys={} seed={}", n_polys, seed);
            let ratio = if pp_med == 0 {
                "inf".to_string()
            } else {
                format!("{:.2}x", f4_med as f64 / pp_med as f64)
            };
            let verdict = if pp_trivial { "trivial" } else { "ok" };
            println!(
                "{:<10} | {:>6} | {:>10} | {:>10} | {:>10} | {}",
                n_polys, seed, pp_med, f4_med, ratio, verdict
            );
        }
    }
}
