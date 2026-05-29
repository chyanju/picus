use super::*;

fn run(src: &str) -> Vec<SessionOutput> {
    let mut s = SmtSession::new();
    s.eval_script(src).expect("script ok")
}

fn run_with(s: &mut SmtSession, src: &str) -> Vec<SessionOutput> {
    s.eval_script(src).expect("script ok")
}

fn last_verdict(out: &[SessionOutput]) -> Option<SessionVerdict> {
    for o in out.iter().rev() {
        if let SessionOutput::CheckSat(v) = o {
            return Some(*v);
        }
    }
    None
}

// ────────── Default state ──────────

#[test]
fn new_starts_at_level_zero_no_check() {
    let s = SmtSession::new();
    assert_eq!(s.decision_level(), 0);
    assert!(s.last_verdict().is_none());
    assert!(s.last_model().is_none());
}

// ────────── Trivial scripts ──────────

#[test]
fn exit_terminates_script() {
    // Commands after (exit) must not be evaluated.
    let out = run("(set-logic QF_FF) (exit) (echo \"unreachable\")");
    assert!(out.is_empty() || !matches!(out.last(), Some(SessionOutput::Echo(_))));
}

#[test]
fn echo_emits_string() {
    let out = run("(echo \"hello\")");
    // The echo atom from the tokenizer keeps the surrounding quotes,
    // so the payload contains `hello` as a substring rather than being
    // exactly `hello`. Just assert the output kind + substring.
    let echoed = match out.last() {
        Some(SessionOutput::Echo(s)) => s.clone(),
        other => panic!("expected Echo, got {:?}", other),
    };
    assert!(
        echoed.contains("hello"),
        "echo payload missing 'hello': {:?}",
        echoed
    );
}

#[test]
fn set_info_set_logic_are_silent() {
    let out = run("(set-logic QF_FF) (set-info :name x)");
    assert!(out.is_empty());
}

// ────────── declare + assert + check-sat (FF) ──────────

#[test]
fn ff_sat_via_finitefield_sort() {
    // x: FF7, x + 6 = 0 → x = 1 (mod 7). SAT.
    let out = run(r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= (ff.add x #f6m7) #f0m7))
            (check-sat)
        "#);
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

#[test]
fn ff_unsat_via_contradiction() {
    // x = 1 ∧ x = 2 → UNSAT.
    let out = run(r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (assert (= x #f2m7))
            (check-sat)
        "#);
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
}

// ────────── push / pop levels ──────────

#[test]
fn push_pop_isolates_assertions() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (push)
            (assert (= x #f2m7))
        "#,
    );
    // Inside push: x=1 ∧ x=2 → UNSAT.
    let out = run_with(&mut s, "(check-sat)");
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
    // Pop and re-check: x=1 alone → SAT.
    let out = run_with(&mut s, "(pop) (check-sat)");
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

#[test]
fn pop_past_zero_is_noop() {
    let mut s = SmtSession::new();
    // (pop) at level 0 must not panic; subsequent commands still work.
    let _ = s
        .eval_script("(pop)")
        .expect("pop at level 0 should not error");
    assert_eq!(s.decision_level(), 0);
}

// ────────── reset / reset-assertions ──────────

#[test]
fn reset_clears_everything() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
            (reset)
        "#,
    );
    assert!(s.last_verdict().is_none());
    // After reset, can run a fresh, unrelated session.
    let out = run_with(
        &mut s,
        r#"
            (declare-fun y () (_ FiniteField 11))
            (assert (= y #f3m11))
            (check-sat)
        "#,
    );
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

#[test]
fn reset_assertions_keeps_declarations() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (assert (= x #f2m7))
            (check-sat)
            (reset-assertions)
        "#,
    );
    // Declaration of x kept; reset-assertions only cleared asserts.
    let out = run_with(
        &mut s,
        r#"
            (assert (= x #f3m7))
            (check-sat)
        "#,
    );
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

// ────────── get-value / get-unsat-core ──────────

#[test]
fn get_unsat_core_returns_names_after_unsat() {
    let mut s = SmtSession::new();
    let out = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f1m7) :named a))
            (assert (! (= x #f2m7) :named b))
            (check-sat)
            (get-unsat-core)
        "#,
    );
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
    // The core is some subset of named asserts (may be `[a, b]` or empty
    // depending on how the solver attributes; checking presence here).
    let has_core = out.iter().any(|o| matches!(o, SessionOutput::UnsatCore(_)));
    assert!(has_core, "expected an UnsatCore output");
}

// ────────── (set-option :tlimit-per N) ──────────

#[test]
fn set_option_tlimit_per_is_silent() {
    let out = run("(set-option :tlimit-per 1000)");
    assert!(out.is_empty());
}

// ────────── Bool sort + propositional check-sat ──────────

#[test]
fn bool_only_check_sat() {
    let out = run(r#"
            (declare-fun a () Bool)
            (declare-fun b () Bool)
            (assert (or a b))
            (check-sat)
        "#);
    // Default prime when no FF appears is 2; the assert is SAT.
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}
