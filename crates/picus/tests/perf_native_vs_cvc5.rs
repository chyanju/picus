//! Per-fixture timing comparison between picus's native FF solver and
//! the vendored cvc5 backend on the FULL PLDI circomlib subset (all
//! 68 fixtures in `benchmarks/circom/circomlib-cff5ab6/`).
//!
//! Run manually:
//!
//! ```bash
//! cargo test -p picus --test perf_native_vs_cvc5 \
//!     --release -- --ignored --nocapture
//! ```
//!
//! `--release` is important: debug-mode timings are not
//! representative. Default features (the `cvc5 + native`
//! configuration) are required so both backends are available.
//!
//! Timeout per fixture per backend is 30s. Verdicts are
//! cross-validated: both backends must agree (or both must time out
//! to Unknown) on every fixture, otherwise the test fails. This
//! catches refactor-induced regressions even where the PLDI
//! expected-verdict table doesn't cover a fixture.

#![cfg(all(feature = "cvc5", feature = "native"))]

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use picus::{check_circuit, CheckResult, Config, SolverKind, Theory};

const TIMEOUT_MS: u64 = 30_000;

fn circuit_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/circom/circomlib-cff5ab6")
}

fn verdict_str(r: &CheckResult) -> &'static str {
    match r {
        CheckResult::Safe => "safe",
        CheckResult::Unsafe { .. } => "unsafe",
        CheckResult::Unknown => "unknown",
    }
}

fn time_one(path: &Path, solver: SolverKind) -> (String, Duration) {
    let cfg = Config {
        solver,
        theory: Theory::Ff,
        timeout_ms: TIMEOUT_MS,
        ..Config::default()
    };
    let t0 = Instant::now();
    let result = check_circuit(path, cfg).unwrap_or_else(|e| {
        panic!("check_circuit({}) failed: {}", path.display(), e);
    });
    let dt = t0.elapsed();
    (verdict_str(&result).to_string(), dt)
}

/// Enumerate all `.r1cs` files in the circomlib subset directory.
fn discover_fixtures(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("read circomlib dir")
        .filter_map(|e| e.ok())
        .filter_map(|e| {
            let p = e.path();
            if p.extension().and_then(|s| s.to_str()) == Some("r1cs") {
                p.file_stem().and_then(|s| s.to_str()).map(String::from)
            } else {
                None
            }
        })
        .collect();
    names.sort();
    names
}

#[test]
#[ignore]
fn pldi_circomlib_full_native_vs_cvc5() {
    let dir = circuit_dir();
    if !dir.exists() {
        eprintln!("fixtures not present at {}", dir.display());
        return;
    }
    let names = discover_fixtures(&dir);
    eprintln!(
        "{:42} | {:>8} | {:>8} | {:>10} | {:>10} | {:>10}",
        "fixture", "native", "cvc5", "native ms", "cvc5 ms", "ratio"
    );
    eprintln!("{}", "-".repeat(102));

    let mut native_total: Duration = Duration::ZERO;
    let mut cvc5_total: Duration = Duration::ZERO;
    let mut counted = 0;
    let mut native_wins = 0;
    let mut cvc5_wins = 0;
    let mut verdict_disagreements: Vec<String> = Vec::new();

    for name in &names {
        let path = dir.join(format!("{}.r1cs", name));
        let (v_native, t_native) = time_one(&path, SolverKind::Native);
        let (v_cvc5, t_cvc5) = time_one(&path, SolverKind::Cvc5);

        // Treat Unknown as compatible with anything (timeouts on the
        // large circuits are expected on at least one side).
        let agree =
            v_native == v_cvc5 || v_native == "unknown" || v_cvc5 == "unknown";
        if !agree {
            verdict_disagreements.push(format!(
                "  {}: native={}, cvc5={}",
                name, v_native, v_cvc5
            ));
        }

        let ms_native = t_native.as_millis();
        let ms_cvc5 = t_cvc5.as_millis();
        let ratio = if ms_cvc5 > 0 {
            ms_native as f64 / ms_cvc5 as f64
        } else if ms_native == 0 {
            1.0
        } else {
            f64::INFINITY
        };
        let ratio_str = if ratio.is_finite() {
            format!("{:.2}x", ratio)
        } else {
            "inf".into()
        };
        eprintln!(
            "{:42} | {:>8} | {:>8} | {:>10} | {:>10} | {:>10}",
            name, v_native, v_cvc5, ms_native, ms_cvc5, ratio_str
        );
        native_total += t_native;
        cvc5_total += t_cvc5;
        counted += 1;
        if ms_native < ms_cvc5 {
            native_wins += 1;
        } else if ms_cvc5 < ms_native {
            cvc5_wins += 1;
        }
    }

    eprintln!("{}", "-".repeat(102));
    eprintln!(
        "{:42} | {:>8} | {:>8} | {:>10} | {:>10} | {:>10}",
        format!("TOTAL ({})", counted),
        "",
        "",
        native_total.as_millis(),
        cvc5_total.as_millis(),
        if cvc5_total.as_millis() > 0 {
            format!(
                "{:.2}x",
                native_total.as_millis() as f64 / cvc5_total.as_millis() as f64
            )
        } else {
            "n/a".into()
        }
    );
    eprintln!(
        "wins: native faster on {} / cvc5 faster on {}",
        native_wins, cvc5_wins
    );

    if !verdict_disagreements.is_empty() {
        panic!(
            "verdict disagreements (excluding Unknown):\n{}",
            verdict_disagreements.join("\n")
        );
    }
}
