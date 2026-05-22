//! Stand-alone CLI driving a QF_FF SMT-LIB v2 script through
//! [`picus_solver::smt2::SmtSession`].
//!
//! Usage:
//!   run_smt2 <file.smt2> [iters]
//!
//! Default (`iters` omitted or 1): the script is evaluated once and
//! every non-silent command's response is printed in source order
//! using SMT-LIB-compatible formatting (`sat` / `unsat` / `unknown`,
//! `(model ...)` blocks, `(get-value ...)` responses, `(echo ...)`).
//!
//! With `iters >= 2`: the script is re-evaluated `iters` times, and a
//! CSV-style timing line is printed instead:
//!   `file,verdicts,iters,med_us,min_us,max_us`
//! where `verdicts` is a `|`-separated list of every `(check-sat)`
//! response from the first run.

use std::time::Instant;

use picus_solver::smt2::{SessionOutput, SessionVerdict, SmtSession};

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

    if iters <= 1 {
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(&src).unwrap_or_else(|e| {
            eprintln!("eval {}: {:?}", path, e);
            std::process::exit(1);
        });
        for o in &outs {
            let line = o.to_smtlib();
            if !line.is_empty() {
                println!("{}", line);
            }
        }
        return;
    }

    // Timed mode. Evaluate once to collect verdicts, then time `iters`
    // additional runs.
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(&src).unwrap_or_else(|e| {
        eprintln!("eval {}: {:?}", path, e);
        std::process::exit(1);
    });
    let verdicts: Vec<&str> = outs
        .iter()
        .filter_map(|o| match o {
            SessionOutput::CheckSat(SessionVerdict::Sat) => Some("sat"),
            SessionOutput::CheckSat(SessionVerdict::Unsat) => Some("unsat"),
            SessionOutput::CheckSat(SessionVerdict::Unknown) => Some("unknown"),
            _ => None,
        })
        .collect();
    let verdict_str = verdicts.join("|");

    let mut times = Vec::with_capacity(iters);
    for _ in 0..iters {
        let mut s = SmtSession::new();
        let t = Instant::now();
        let _ = s.eval_script(&src);
        times.push(t.elapsed().as_micros() as u64);
    }
    times.sort();
    let med = times[iters / 2];
    let min = *times.first().unwrap();
    let max = *times.last().unwrap();
    let name = std::path::Path::new(path)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or(path);
    println!("{},{},{},{},{},{}", name, verdict_str, iters, med, min, max);
}
