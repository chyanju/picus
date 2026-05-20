//! Stand-alone CLI that solves a QF_FF SMT-LIB v2 file via picus-solver.
//!
//! Usage:
//!   run_smt2 <file.smt2> [iters]
//!
//! With `iters` omitted or 1: prints one of `sat` / `unsat` / `unknown`.
//! With `iters >= 2`: also prints a CSV-style timing line:
//!   `file,verdict,iters,encode_us,gb_med_us,gb_min_us,gb_max_us,total_med_us`
//! where `encode_us` is the one-shot encode time, `gb_*` are over
//! `iters` solve invocations on a single encoded system, and
//! `total_med_us` is the median over `iters` encode+solve cycles.

use std::time::Instant;

use picus_solver::core::{solve_encoded, SolveOutcome};
use picus_solver::encoder::encode;
use picus_solver::smt2;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: {} <file.smt2> [iters]", args[0]);
        std::process::exit(2);
    }
    let path = &args[1];
    let iters: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);

    let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("read {}: {}", path, e);
        std::process::exit(1);
    });
    let cs = smt2::parse(&src).unwrap_or_else(|e| {
        eprintln!("parse {}: {}", path, e);
        std::process::exit(1);
    });

    let t0 = Instant::now();
    let encoded = encode(&cs).unwrap_or_else(|e| {
        eprintln!("encode {}: {}", path, e);
        std::process::exit(1);
    });
    let encode_us = t0.elapsed().as_micros() as u64;

    let outcome = solve_encoded(&encoded);
    let verdict = match outcome {
        SolveOutcome::Sat(_) => "sat",
        SolveOutcome::Unsat(_) => "unsat",
        SolveOutcome::Unknown => "unknown",
    };

    if iters <= 1 {
        println!("{}", verdict);
        return;
    }

    // iters >= 2: emit a CSV-style timing line.
    let mut solve_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        let _ = solve_encoded(&encoded);
        solve_times.push(t.elapsed().as_micros() as u64);
    }
    solve_times.sort();
    let med = solve_times[iters / 2];
    let min = *solve_times.first().unwrap();
    let max = *solve_times.last().unwrap();

    let mut total_times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let t = Instant::now();
        let enc = encode(&cs).expect("encode");
        let _ = solve_encoded(&enc);
        total_times.push(t.elapsed().as_micros() as u64);
    }
    total_times.sort();
    let total_med = total_times[iters / 2];

    let name = std::path::Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(path);
    println!(
        "{},{},{},{},{},{},{},{}",
        name, verdict, iters, encode_us, med, min, max, total_med
    );
}
