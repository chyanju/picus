//! End-to-end R1CS smoke test against a curated `circomlib-cff5ab6`
//! subset, run through the native finite-field backend.
//!
//! Acts as a refactor gate complementing the unit tests in
//! `picus-solver`: every fixture's verdict is verified to match the
//! expected `safe` / `unsafe` outcome documented in
//! `docs/benchmarks.md`.
//!
//! The test reads compiled `.r1cs` files from the `benchmarks/circom/`
//! submodule. If the submodule is not initialised or the circuits are
//! not yet compiled, the test logs a hint and exits 0 (so a clean
//! checkout still passes `cargo test`).
//!
//! To provision the fixtures:
//!
//! ```bash
//! git submodule update --init benchmarks
//! cd benchmarks/circom && ./compile.sh build circomlib-cff5ab6
//! ```

use std::path::PathBuf;

use picus::{check_circuit, CheckResult, Config, SolverKind, Theory};

/// `(circuit_name, expected_verdict)` pairs. Expected verdicts mirror
/// `docs/benchmarks.md § Expected Results` for `circomlib-cff5ab6`.
/// Selected for small `.r1cs` size and fast verdict under the native
/// solver — the known slow / never-resolved circuits (Pedersen,
/// BitElementMulAny, ed25519 / keccak / pairing) are excluded.
const FIXTURES: &[(&str, &str)] = &[
    // safe-expected
    ("AND@gates", "safe"),
    ("OR@gates", "safe"),
    ("NAND@gates", "safe"),
    ("IsZero@comparators", "safe"),
    ("IsEqual@comparators", "safe"),
    ("Mux1@mux1", "safe"),
    ("Switcher@switcher", "safe"),
    ("Sigma@poseidon", "safe"),
    ("MultiAND@gates", "safe"),
    ("MultiMux1@mux1", "safe"),
    // unsafe-expected
    ("Decoder@multiplexer", "unsafe"),
    ("Edwards2Montgomery@montgomery", "unsafe"),
    ("Montgomery2Edwards@montgomery", "unsafe"),
    ("MontgomeryAdd@montgomery", "unsafe"),
    ("MontgomeryDouble@montgomery", "unsafe"),
    ("Bits2Point@pointbits", "unsafe"),
    ("Point2Bits@pointbits", "unsafe"),
];

/// `benchmarks/circom/circomlib-cff5ab6/` relative to the workspace
/// root, derived from `CARGO_MANIFEST_DIR`
/// (= `crates/picus/`).
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

#[test]
fn r1cs_smoke_native_ff() {
    let dir = circuit_dir();
    if !dir.exists() {
        eprintln!(
            "r1cs_smoke: {} not present — initialise the submodule and \
             compile the circuits (see test docstring); skipping.",
            dir.display()
        );
        return;
    }

    let cfg = Config {
        solver: SolverKind::Native,
        theory: Theory::Ff,
        timeout_ms: 5000,
        ..Config::default()
    };

    let mut missing: Vec<&str> = Vec::new();
    let mut failures: Vec<String> = Vec::new();
    let mut passed = 0usize;

    for (name, expected) in FIXTURES {
        let path = dir.join(format!("{}.r1cs", name));
        if !path.exists() {
            missing.push(*name);
            continue;
        }
        let result = check_circuit(&path, cfg.clone()).unwrap_or_else(|e| {
            panic!("check_circuit({}) failed: {}", name, e);
        });
        let actual = verdict_str(&result);
        if actual == *expected {
            passed += 1;
        } else {
            failures.push(format!(
                "  {:44} expected {}, got {}",
                name, expected, actual
            ));
        }
    }

    eprintln!(
        "r1cs_smoke: {} / {} fixtures passed ({} missing)",
        passed,
        FIXTURES.len() - missing.len(),
        missing.len()
    );
    if !missing.is_empty() {
        eprintln!(
            "  missing .r1cs files (run benchmarks/circom/compile.sh): {:?}",
            missing
        );
    }
    if !failures.is_empty() {
        panic!("r1cs_smoke verdict mismatches:\n{}", failures.join("\n"));
    }
}
