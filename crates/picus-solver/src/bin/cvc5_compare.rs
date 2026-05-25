//! cvc5 vs picus-solver wall-time comparison on the `bench_fixtures`
//! corpus.
//!
//! Usage:
//!
//! ```text
//! cargo run --release --bin cvc5_compare -- [--cvc5 <path>] [--timeout-ms N] [--iters K]
//! ```
//!
//! Each fixture is written to a temp `.smt2` file once. cvc5 is
//! invoked with `--ff-solver split` for `iters` repetitions (median
//! reported). picus-solver runs in-process via `parse_boolean +
//! solve_formula` for the same number of repetitions.

use std::env;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

use picus_solver::frontend::bench_fixtures::corpus;
use picus_solver::cdclt::solve_formula;
use picus_solver::core::SolveOutcome;
use picus_solver::smt2::parse_boolean;
use picus_core::timeout::CancelToken;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
    Error,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
            Verdict::Error => "error",
        }
    }
}

fn picus_solve(src: &str, timeout_ms: u64) -> (Verdict, Duration) {
    let t0 = Instant::now();
    let q = match parse_boolean(src) {
        Ok(q) => q,
        Err(_) => return (Verdict::Error, t0.elapsed()),
    };
    let cancel = CancelToken::with_timeout(Duration::from_millis(timeout_ms));
    let v = match solve_formula(q.prime.clone(), q.var_names(), &q.formula, &cancel) {
        SolveOutcome::Sat(_) => Verdict::Sat,
        SolveOutcome::Unsat(_) => Verdict::Unsat,
        SolveOutcome::Unknown => Verdict::Unknown,
    };
    (v, t0.elapsed())
}

fn cvc5_solve(cvc5: &str, smt2_path: &str, timeout_ms: u64) -> (Verdict, Duration) {
    let t0 = Instant::now();
    let output = Command::new(cvc5)
        .arg("--lang")
        .arg("smt2")
        .arg("--ff-solver")
        .arg("split")
        .arg("--tlimit-per")
        .arg(&format!("{}", timeout_ms))
        .arg(smt2_path)
        .output();
    let dt = t0.elapsed();
    let stdout = match output {
        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().to_string(),
        Err(_) => return (Verdict::Error, dt),
    };
    let first = stdout.lines().next().unwrap_or("").trim();
    let v = match first {
        "sat" => Verdict::Sat,
        "unsat" => Verdict::Unsat,
        "unknown" => Verdict::Unknown,
        _ => Verdict::Error,
    };
    (v, dt)
}

fn median(xs: &mut [Duration]) -> Duration {
    xs.sort();
    xs[xs.len() / 2]
}

fn fmt_dur(d: Duration) -> String {
    let us = d.as_secs_f64() * 1_000_000.0;
    if us < 1_000.0 {
        format!("{:.0} µs", us)
    } else if us < 1_000_000.0 {
        format!("{:.1} ms", us / 1_000.0)
    } else {
        format!("{:.2} s", us / 1_000_000.0)
    }
}

struct Args {
    cvc5: String,
    timeout_ms: u64,
    iters: usize,
}

fn parse_args() -> Args {
    let default_cvc5 = "/home/ubuntu/Downloads/suite-picus/picus/target/release/build/cvc5-ff-sys-12df471d7dc7fff0/out/cvc5/build/bin/cvc5";
    let mut a = Args {
        cvc5: default_cvc5.to_string(),
        timeout_ms: 10_000,
        iters: 3,
    };
    let args: Vec<String> = env::args().collect();
    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "--cvc5" => {
                a.cvc5 = args[i + 1].clone();
                i += 2;
            }
            "--timeout-ms" => {
                a.timeout_ms = args[i + 1].parse().expect("--timeout-ms expects integer");
                i += 2;
            }
            "--iters" => {
                a.iters = args[i + 1].parse().expect("--iters expects integer");
                i += 2;
            }
            _ => {
                eprintln!("ignoring arg: {}", args[i]);
                i += 1;
            }
        }
    }
    a
}

fn main() {
    let args = parse_args();
    let cvc5 = &args.cvc5;
    let timeout_ms = args.timeout_ms;
    let iters = args.iters;
    eprintln!(
        "cvc5={}  timeout_per_query={}ms  iters={}",
        cvc5, timeout_ms, iters
    );

    let tmpdir = std::env::temp_dir().join("picus_cvc5_compare");
    fs::create_dir_all(&tmpdir).expect("mkdir tmp");
    let header = format!(
        "{:<22}  {:<24}  {:>5}  {:>5}  {:>11}  {:>11}  {:>9}",
        "family", "label", "p_v", "c_v", "picus_med", "cvc5_med", "cvc5/picus"
    );
    println!("{}", header);
    println!("{}", "-".repeat(header.len()));

    for (family, label, src) in corpus() {
        let mut path: PathBuf = tmpdir.clone();
        path.push(format!("{}__{}.smt2", family, label));
        let mut f = fs::File::create(&path).expect("write smt2");
        f.write_all(src.as_bytes()).expect("write smt2");
        let smt2_path = path.to_string_lossy().to_string();

        let mut picus_times: Vec<Duration> = Vec::with_capacity(iters);
        let mut picus_verdicts: Vec<Verdict> = Vec::with_capacity(iters);
        for k in 0..iters {
            let (v, d) = picus_solve(&src, timeout_ms);
            picus_verdicts.push(v);
            picus_times.push(d);
            // After the first iteration: if picus took close to or
            // above the timeout, skip further iterations on this
            // fixture to keep the overall run bounded.
            if k == 0 && d.as_millis() as u64 + 200 >= timeout_ms {
                break;
            }
        }
        let p_verdict = picus_verdicts[0];

        let mut cvc5_times: Vec<Duration> = Vec::with_capacity(iters);
        let mut cvc5_verdicts: Vec<Verdict> = Vec::with_capacity(iters);
        for k in 0..iters {
            let (v, d) = cvc5_solve(cvc5, &smt2_path, timeout_ms);
            cvc5_verdicts.push(v);
            cvc5_times.push(d);
            if k == 0 && d.as_millis() as u64 + 200 >= timeout_ms {
                break;
            }
        }
        let c_verdict = cvc5_verdicts[0];

        let p_med = median(&mut picus_times);
        let c_med = median(&mut cvc5_times);
        let ratio = if p_med.as_nanos() > 0 {
            c_med.as_secs_f64() / p_med.as_secs_f64()
        } else {
            f64::NAN
        };
        println!(
            "{:<22}  {:<24}  {:>5}  {:>5}  {:>11}  {:>11}  {:>8.2}x",
            family,
            label,
            p_verdict.label(),
            c_verdict.label(),
            fmt_dur(p_med),
            fmt_dur(c_med),
            ratio,
        );
    }
}
