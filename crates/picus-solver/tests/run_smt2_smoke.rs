//! End-to-end smoke tests for the `run_smt2` binary.
//!
//! These tests build the binary's input (an SMT-LIB v2 script
//! exercising every multi-command response the driver should print)
//! and run the binary as a subprocess. Each test asserts that the
//! captured stdout contains the expected SMT-LIB v2 response lines.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

fn binary_path() -> PathBuf {
    // CARGO_BIN_EXE_<name> is set by Cargo for integration tests.
    PathBuf::from(env!("CARGO_BIN_EXE_run_smt2"))
}

fn run_with(input: &str) -> String {
    let dir = std::env::temp_dir();
    let path = dir.join(format!(
        "picus_run_smt2_smoke_{}.smt2",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    {
        let mut f = std::fs::File::create(&path).unwrap();
        f.write_all(input.as_bytes()).unwrap();
    }
    let out = Command::new(binary_path())
        .arg(&path)
        .output()
        .expect("spawn run_smt2");
    std::fs::remove_file(&path).ok();
    assert!(out.status.success(), "exit={:?} stderr={}",
        out.status,
        String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn smoke_check_sat_only() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f3m7))
(check-sat)
"#,
    );
    assert_eq!(stdout.trim(), "sat");
}

#[test]
fn smoke_check_sat_unsat() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f2m7))
(assert (= x #f3m7))
(check-sat)
"#,
    );
    assert_eq!(stdout.trim(), "unsat");
}

#[test]
fn smoke_get_model_and_get_value() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(declare-fun b () Bool)
(assert (= x #f3m7))
(assert b)
(check-sat)
(get-model)
(get-value (x b))
"#,
    );
    // sat verdict
    assert!(stdout.lines().any(|l| l.trim() == "sat"));
    // model define-fun lines
    assert!(stdout.contains("(define-fun x () (_ FiniteField 7) #f3m7)"));
    assert!(stdout.contains("(define-fun b () Bool true)"));
    // get-value pair list
    assert!(stdout.contains("(x #f3m7)"));
    assert!(stdout.contains("(b true)"));
}

#[test]
fn smoke_push_pop_returns_three_verdicts() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f3m7))
(check-sat)
(push 1)
(assert (= x #f5m7))
(check-sat)
(pop 1)
(check-sat)
"#,
    );
    let verdicts: Vec<&str> = stdout
        .lines()
        .filter_map(|l| match l.trim() {
            "sat" | "unsat" | "unknown" => Some(l.trim()),
            _ => None,
        })
        .collect();
    assert_eq!(verdicts, vec!["sat", "unsat", "sat"]);
}

#[test]
fn smoke_named_assert_and_get_unsat_core() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (! (= x #f2m7) :named a))
(assert (! (= x #f3m7) :named b))
(check-sat)
(get-unsat-core)
"#,
    );
    assert!(stdout.lines().any(|l| l.trim() == "unsat"));
    // The core line contains both a and b (order is the assert order).
    let core_line = stdout
        .lines()
        .find(|l| l.starts_with("(") && l.contains("a") && l.contains("b"))
        .expect("core line not found");
    assert!(core_line.contains("a") && core_line.contains("b"));
}

#[test]
fn smoke_exit_truncates_output() {
    let stdout = run_with(
        r#"(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f3m7))
(check-sat)
(exit)
(assert (= x #f4m7))
(check-sat)
"#,
    );
    let verdicts: Vec<&str> = stdout
        .lines()
        .filter_map(|l| match l.trim() {
            "sat" | "unsat" | "unknown" => Some(l.trim()),
            _ => None,
        })
        .collect();
    assert_eq!(verdicts, vec!["sat"]);
}
