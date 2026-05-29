//! `SmtSession`-level integration tests (formerly inside `tests.rs`).
//!
//! These exercise the script-eval surface from `mod.rs`: `(set-logic)`,
//! declarations, `(assert)`, `(check-sat)`, `(get-model)`, `(get-value)`,
//! `(get-unsat-core)`, `(push)`/`(pop)`, `(reset)`/`(reset-assertions)`,
//! `(set-option :tlimit-per ...)`, `(! ... :named ...)` annotations and
//! adversarial-input robustness via `eval_script`.
//!
//! Each test is its own `#[test]`; helper-free (every test instantiates
//! `SmtSession::new()` directly), so this file has no shared scaffolding.

use super::*;

// ─────────────────────────── SmtSession ─────────────────────────

// `session_check_sat_returns_sat_for_satisfiable` deleted: subsumed by
// session_tests.rs `prop_single_value_assertion_sat_across_edge_primes`
// (asserts the same `x = constant` SAT property across primes 2/3/5/7/11).
//
// `session_check_sat_returns_unsat` deleted: subsumed by session_tests.rs
// `prop_contradictory_constants_unsat_across_edge_primes` (asserts the
// same `x=a ∧ x=b, a≠b` UNSAT property across primes 3/5/7/11/13).

#[test]
fn session_get_model_prints_assignment() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (declare-fun b () Bool)
        (assert (= x #f3m7))
        (assert b)
        (check-sat)
        (get-model)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 2);
    assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
    let model_text = match &outs[1] {
        SessionOutput::Model(s) => s.clone(),
        other => panic!("expected Model, got {:?}", other),
    };
    assert!(
        model_text.contains("(define-fun x () (_ FiniteField 7) #f3m7)"),
        "missing x; model:\n{}",
        model_text
    );
    assert!(
        model_text.contains("(define-fun b () Bool true)"),
        "missing b=true; model:\n{}",
        model_text
    );
}

#[test]
fn session_get_value_prints_requested() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (declare-fun b () Bool)
        (assert (= x #f3m7))
        (assert (not b))
        (check-sat)
        (get-value (x b))
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 2);
    let values = match &outs[1] {
        SessionOutput::Values(v) => v.clone(),
        other => panic!("expected Values, got {:?}", other),
    };
    assert_eq!(values.len(), 2);
    assert_eq!(values[0], ("x".into(), "#f3m7".into()));
    assert_eq!(values[1], ("b".into(), "false".into()));
}

#[test]
fn session_push_pop_isolates_asserts() {
    // Stack: base (sat) → push (add contradicting assert → unsat)
    // → pop (sat again).
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
        (push 1)
        (assert (= x #f5m7))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    let verdicts: Vec<SessionVerdict> = outs
        .iter()
        .filter_map(|o| if let SessionOutput::CheckSat(v) = o { Some(*v) } else { None })
        .collect();
    assert_eq!(
        verdicts,
        vec![SessionVerdict::Sat, SessionVerdict::Unsat, SessionVerdict::Sat]
    );
}

#[test]
fn session_pop_drops_declared_vars() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (push 1)
        (declare-fun y () (_ FiniteField 7))
        (assert (= y #f4m7))
        (pop 1)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert!(sess.vars.contains_key("x"));
    assert!(!sess.vars.contains_key("y"), "y must be dropped after pop");
    assert_eq!(sess.formulas.len(), 0, "y's assert must be dropped");
}

#[test]
fn session_multiple_check_sat_independent() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
        (check-sat)
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 3);
    for o in &outs {
        assert!(matches!(o, SessionOutput::CheckSat(SessionVerdict::Sat)));
    }
}

#[test]
fn session_to_smtlib_formats_verdicts() {
    assert_eq!(
        SessionOutput::CheckSat(SessionVerdict::Sat).to_smtlib(),
        "sat"
    );
    assert_eq!(
        SessionOutput::CheckSat(SessionVerdict::Unsat).to_smtlib(),
        "unsat"
    );
    assert_eq!(
        SessionOutput::CheckSat(SessionVerdict::Unknown).to_smtlib(),
        "unknown"
    );
}

// `session_named_assert_strips_annotation` deleted: strict subset of
// `session_named_annotation_with_other_attrs_is_stripped` below, which
// exercises two `:named` asserts (foo + bar) PLUS a generic `:weight`
// attribute on the same form, covering both the strip-and-solve and the
// label-capture paths in one go.

#[test]
fn session_get_unsat_core_reports_named_asserts() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (! (= x #f2m7) :named a))
        (assert (! (= x #f3m7) :named b))
        (check-sat)
        (get-unsat-core)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 2);
    assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Unsat)));
    match &outs[1] {
        SessionOutput::UnsatCore(names) => {
            assert!(names.contains(&"a".to_string()) && names.contains(&"b".to_string()),
                "core must include both named asserts; got {:?}", names);
        }
        other => panic!("expected UnsatCore, got {:?}", other),
    }
}

#[test]
fn session_get_unsat_core_empty_on_sat() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (! (= x #f5m7) :named foo))
        (check-sat)
        (get-unsat-core)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    match &outs[1] {
        SessionOutput::UnsatCore(names) => assert!(
            names.is_empty(),
            "SAT verdict ⇒ empty core; got {:?}",
            names
        ),
        other => panic!("expected UnsatCore, got {:?}", other),
    }
}

#[test]
fn session_unnamed_asserts_excluded_from_core() {
    // Only the `:named` asserts should appear in the core.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f2m7))
        (assert (! (= x #f3m7) :named conflict))
        (check-sat)
        (get-unsat-core)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    match &outs[1] {
        SessionOutput::UnsatCore(names) => {
            assert_eq!(names, &vec!["conflict".to_string()]);
        }
        other => panic!("expected UnsatCore, got {:?}", other),
    }
}

// `session_set_option_tlimit_per_is_recorded` deleted: subsumed by
// session_tests.rs `set_option_tlimit_per_zero_disables`, which seeds the
// session to `Some(1000)` via the same `:tlimit-per N` path and asserts
// that recorded value before then transitioning to 0 → None.

#[test]
fn session_tlimit_per_zero_disables_timeout() {
    let src = r#"
        (set-option :tlimit-per 0)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.tlimit_per_ms, None);
}

// ─── Edge cases: queries-before-check, exit, reset variants ───

#[test]
fn session_get_model_before_check_sat_returns_empty_model() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (get-model)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 1);
    match &outs[0] {
        // No check-sat ran ⇒ no model recorded ⇒ empty block.
        SessionOutput::Model(s) => {
            assert!(!s.contains("define-fun"), "no defs expected; got {:?}", s);
        }
        other => panic!("expected Model, got {:?}", other),
    }
}

// `session_get_value_before_check_sat_returns_empty` deleted: identical
// property to session_tests.rs `get_value_without_model_is_empty`
// (declared x, no prior check-sat, get-value yields empty Values list).

#[test]
fn session_get_value_skips_undeclared_name() {
    // Querying an undeclared name must skip it rather than
    // fabricate a zero value.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
        (get-value (x undeclared))
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    let values = match &outs[1] {
        SessionOutput::Values(v) => v.clone(),
        other => panic!("expected Values, got {:?}", other),
    };
    assert_eq!(values.len(), 1, "undeclared name must be skipped: {:?}", values);
    assert_eq!(values[0].0, "x");
}

#[test]
fn session_get_unsat_core_before_check_sat_is_empty() {
    let src = r#"
        (set-logic QF_FF)
        (get-unsat-core)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    match &outs[0] {
        SessionOutput::UnsatCore(v) => assert!(v.is_empty()),
        other => panic!("expected UnsatCore, got {:?}", other),
    }
}

#[test]
fn session_exit_stops_eval_script() {
    // Commands after `(exit)` must not be evaluated.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
        (exit)
        (assert (= x #f4m7))
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    // Exactly one (check-sat) before (exit) — the trailing one is skipped.
    let verdicts: Vec<_> = outs
        .iter()
        .filter_map(|o| if let SessionOutput::CheckSat(v) = o { Some(*v) } else { None })
        .collect();
    assert_eq!(verdicts, vec![SessionVerdict::Sat]);
    // The trailing assert was never applied to session state.
    assert_eq!(sess.formulas.len(), 1);
}

#[test]
fn session_reset_clears_everything() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (set-option :tlimit-per 5000)
        (assert (= x #f3m7))
        (reset)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert!(sess.vars.is_empty());
    assert!(sess.formulas.is_empty());
    assert!(sess.prime.is_none());
    assert_eq!(sess.tlimit_per_ms, None);
}

#[test]
fn session_reset_assertions_keeps_declarations() {
    // SMT-LIB v2 §4.2.1: (reset-assertions) clears asserts and
    // the push trail but keeps the logic, declarations, macros,
    // and options.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (define-fun is_three ((y (_ FiniteField 7))) Bool (= y #f3m7))
        (set-option :tlimit-per 4000)
        (assert (is_three x))
        (reset-assertions)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert!(sess.vars.contains_key("x"), "declarations must survive reset-assertions");
    assert!(sess.macros.contains_key("is_three"), "macros must survive");
    assert_eq!(sess.prime, Some(BigUint::from(7u32)));
    assert_eq!(sess.tlimit_per_ms, Some(4000));
    assert!(sess.formulas.is_empty(), "asserts must be cleared");
    assert!(sess.levels.is_empty(), "push trail must be cleared");
}

// ─── Edge cases: push/pop ───

#[test]
fn session_push_n_pop_n_balance() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (push 3)
        (assert (= x #f1m7))
        (push 2)
        (assert (= x #f2m7))
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.decision_level(), 5);
    assert_eq!(sess.formulas.len(), 2);
    // Pop 4 of 5 levels — the top 4 came after the second assert
    // and the first one — both should be cleared.
    sess.eval_script("(pop 4)").expect("eval");
    assert_eq!(sess.decision_level(), 1);
    assert_eq!(sess.formulas.len(), 0);
}

#[test]
fn session_pop_past_root_is_best_effort() {
    // Popping more levels than exist must not panic; remaining
    // requests are no-ops.
    let src = r#"
        (push 2)
        (pop 5)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.decision_level(), 0);
}

// ─── Edge cases: macros / declarations across push/pop ───

#[test]
fn session_macro_introduced_inside_push_is_dropped_on_pop() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (push 1)
        (define-fun is_one ((y (_ FiniteField 7))) Bool (= y #f1m7))
        (assert (is_one x))
        (pop 1)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert!(!sess.macros.contains_key("is_one"), "macro must be dropped");
    assert!(sess.formulas.is_empty(), "assert using macro must be dropped");
}

#[test]
fn session_pop_restores_ite_skolem_counter() {
    // A term-level (ite ...) inside an assert allocates a
    // __ite_N skolem and emits side constraints. After pop, the
    // counter must reset so a new ite re-uses the same name.
    let src_push = r#"
        (set-logic QF_FF)
        (declare-fun c () Bool)
        (declare-fun x () (_ FiniteField 101))
        (push 1)
        (assert (= (ite c x #f0m101) #f5m101))
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src_push).expect("eval");
    let counter_after_assert = sess.next_ite_skolem;
    assert!(counter_after_assert >= 1, "an ite must allocate a skolem");
    sess.eval_script("(pop 1)").expect("eval");
    assert_eq!(
        sess.next_ite_skolem, 0,
        "pop must restore the ite counter to its pre-push value"
    );
    assert!(sess.side_constraints.is_empty(),
        "ite side constraints must be dropped with the push level");
}

// ─── Bool-var iteration determinism ───

#[test]
fn session_bool_constraints_use_declaration_order() {
    // The order of the auto-emitted `b*b = b` constraints is
    // tied to declaration order, not HashMap iteration order.
    // Re-running the same script must produce the same verdict
    // deterministically.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
        (declare-fun d () Bool)
        (declare-fun e () Bool)
        (assert (or a b c d e))
        (check-sat)
    "#;
    for _ in 0..3 {
        let mut sess = SmtSession::new();
        let outs = sess.eval_script(src).expect("eval");
        assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
    }
}

// ─── to_smtlib formatter ───

#[test]
fn session_to_smtlib_formats_values_and_core() {
    let v = SessionOutput::Values(vec![
        ("x".into(), "#f3m7".into()),
        ("b".into(), "true".into()),
    ]);
    let s = v.to_smtlib();
    assert!(s.contains("(x #f3m7)"));
    assert!(s.contains("(b true)"));

    let c = SessionOutput::UnsatCore(vec!["a".into(), "b".into()]);
    assert_eq!(c.to_smtlib(), "(a b)");

    let empty = SessionOutput::UnsatCore(Vec::new());
    assert_eq!(empty.to_smtlib(), "()");
}

// `session_silent_to_smtlib_is_empty_string` deleted: the
// `SessionOutput::Silent → ""` rendering is covered by session_tests.rs
// `to_smtlib_renders_each_session_output_variant`, which sweeps every
// variant including Silent.

// ─── (! ... :named ...) edge cases ───

#[test]
fn session_named_annotation_with_other_attrs_is_stripped() {
    // `(! formula :pattern (...) :named foo :weight 3)` — generic
    // attributes are ignored, but `:named` is captured wherever
    // it appears in the attribute list.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (! (= x #f2m7) :weight 3 :named foo))
        (assert (! (= x #f3m7) :named bar))
        (check-sat)
        (get-unsat-core)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    let core = match &outs[1] {
        SessionOutput::UnsatCore(v) => v.clone(),
        other => panic!("expected UnsatCore, got {:?}", other),
    };
    assert!(core.contains(&"foo".to_string()));
    assert!(core.contains(&"bar".to_string()));
}

// ─── set-option misuse ───
//
// `session_set_option_non_numeric_tlimit_is_ignored` deleted: identical
// property + setup to session_tests.rs `set_option_tlimit_per_non_numeric_is_ignored`.

#[test]
fn session_set_option_tlimit_per_can_be_overwritten() {
    let src = r#"
        (set-option :tlimit-per 1000)
        (set-option :tlimit-per 2000)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.tlimit_per_ms, Some(2000));
}

#[test]
fn session_echo_is_passed_through() {
    let src = r#"(echo "hello")"#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 1);
    match &outs[0] {
        SessionOutput::Echo(s) => assert_eq!(s, "\"hello\""),
        other => panic!("expected Echo, got {:?}", other),
    }
}
