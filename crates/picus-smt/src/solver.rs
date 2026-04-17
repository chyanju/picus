//! SMT solver invocation and result parsing.

use num_bigint::BigUint;
use regex::Regex;
use std::collections::HashMap;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::LazyLock;
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tempfile::NamedTempFile;
use thiserror::Error;

use crate::SolverKind;

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Solver not found: {0}")]
    NotFound(String),
    #[error("Solver error: {0}")]
    SolverErr(String),
}

#[derive(Debug, Clone)]
pub enum SolverResult {
    Unsat,
    Sat(HashMap<String, BigUint>),
    Timeout,
    Unknown,
    Error(String),
}

static LAST_SMT_PATH: LazyLock<Mutex<Option<PathBuf>>> = LazyLock::new(|| Mutex::new(None));

pub fn last_smt_path() -> Option<PathBuf> {
    LAST_SMT_PATH.lock().unwrap().clone()
}

pub fn solve(
    smt_str: &str,
    solver: SolverKind,
    timeout_ms: u64,
) -> Result<SolverResult, SolverError> {
    let ts = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis();
    let mut tmp =
        NamedTempFile::with_prefix(format!("picus{}", ts)).map_err(SolverError::Io)?;
    tmp.write_all(smt_str.as_bytes())?;
    tmp.flush()?;

    let tmp_path = tmp.into_temp_path();
    let path_str = tmp_path.to_str().unwrap().to_string();

    *LAST_SMT_PATH.lock().unwrap() = Some(PathBuf::from(&path_str));

    // z3 uses -T:seconds; cvc5/cvc4 use --tlimit=ms
    let timeout_secs = timeout_ms.div_ceil(1000).max(1);
    let (program, args) = match solver {
        SolverKind::Z3 => (
            "z3",
            vec![format!("-T:{}", timeout_secs), path_str.clone()],
        ),
        SolverKind::Cvc4 => (
            "cvc4",
            vec![
                "--produce-models".into(),
                format!("--tlimit={}", timeout_ms),
                path_str.clone(),
            ],
        ),
        SolverKind::Cvc5 => (
            "cvc5",
            vec![
                "--produce-models".into(),
                format!("--tlimit={}", timeout_ms),
                path_str.clone(),
            ],
        ),
    };

    let mut child = match Command::new(program)
        .args(&args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err(SolverError::NotFound(program.to_string()));
        }
        Err(e) => return Err(SolverError::Io(e)),
    };

    // Read stdout/stderr in threads to avoid pipe deadlock
    let stdout_handle = child.stdout.take();
    let stderr_handle = child.stderr.take();

    let stdout_thread = std::thread::spawn(move || {
        let mut s = String::new();
        if let Some(mut out) = stdout_handle {
            let _ = out.read_to_string(&mut s);
        }
        s
    });
    let stderr_thread = std::thread::spawn(move || {
        let mut s = String::new();
        if let Some(mut err) = stderr_handle {
            let _ = err.read_to_string(&mut s);
        }
        s
    });

    // Wait for child with hard timeout (solver has its own internal timeout,
    // this is a safety net)
    let hard_timeout = Duration::from_millis(timeout_ms + 10000);
    let start = Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_status)) => break,
            Ok(None) => {
                if start.elapsed() >= hard_timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Ok(SolverResult::Timeout);
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(SolverError::Io(e));
            }
        }
    }

    let stdout = stdout_thread.join().unwrap_or_default();
    let stderr = stderr_thread.join().unwrap_or_default();

    log::debug!(
        "Solver stdout ({} bytes): {}",
        stdout.len(),
        &stdout[..stdout.len().min(300)]
    );
    if !stderr.is_empty() {
        log::debug!(
            "Solver stderr ({} bytes): {}",
            stderr.len(),
            &stderr[..stderr.len().min(200)]
        );
    }

    // Check for errors (but only if stdout doesn't start with a valid result)
    if !stderr.is_empty()
        && !stdout.starts_with("sat")
        && !stdout.starts_with("unsat")
        && !stdout.starts_with("unknown")
    {
        return Ok(SolverResult::Error(stderr));
    }

    if stdout.starts_with("unsat") {
        Ok(SolverResult::Unsat)
    } else if stdout.starts_with("sat") {
        let model = parse_model(&stdout);
        Ok(SolverResult::Sat(model))
    } else if stdout.starts_with("unknown") || stdout.contains("timeout") || stdout.is_empty() {
        Ok(SolverResult::Timeout)
    } else {
        Ok(SolverResult::Error(format!(
            "Unexpected: {}",
            &stdout[..stdout.len().min(200)]
        )))
    }
}

fn parse_model(output: &str) -> HashMap<String, BigUint> {
    let mut model = HashMap::new();
    let p = picus_r1cs::bn128_prime();

    let re = Regex::new(r"\(define-fun\s+(\w+)\s+\(\)\s+[^\s]+\s+(-?\d+)\)").unwrap();

    for cap in re.captures_iter(output) {
        let var_name = cap[1].to_string();
        let val_str = &cap[2];

        let val = if let Some(stripped) = val_str.strip_prefix('-') {
            let abs_val: BigUint = stripped.parse().unwrap_or_default();
            if abs_val > p {
                abs_val
            } else {
                &p - &abs_val
            }
        } else {
            val_str.parse().unwrap_or_default()
        };

        model.insert(var_name, val);
    }

    model
}
