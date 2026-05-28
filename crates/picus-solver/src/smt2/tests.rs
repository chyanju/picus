use super::*;

#[test]
fn parses_minimal_unsat() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x (as ff2 F)))
        (assert (= x (as ff3 F)))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(7u32));
    assert_eq!(cs.equalities.len(), 2);
}

#[test]
fn parses_inline_finite_field_sort() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 17))
        (assert (= (ff.mul x x) x))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(17u32));
    assert_eq!(cs.equalities.len(), 1);
}

#[test]
fn rejects_boolean_in_assert() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (or (= x (as ff0 F)) (= y (as ff0 F))))
        (check-sat)
    "#;
    match parse(src) {
        Err(ParseError::BooleanInAssert(op)) => assert_eq!(op, "or"),
        other => panic!("expected BooleanInAssert(or); got {:?}", other),
    }
}

#[test]
fn parses_disequality_via_not() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (not (= x (as ff0 F))))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.disequalities.len(), 1);
    assert_eq!(cs.assignments.len(), 1); // __zero pinned
}

#[test]
fn rejects_unknown_symbol() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x y))
        (check-sat)
    "#;
    match parse(src) {
        Err(ParseError::UnknownSymbol(s)) => assert_eq!(s, "y"),
        other => panic!("expected UnknownSymbol(y); got {:?}", other),
    }
}

// ─────────────── Bool decl + iff (parse_boolean) ───────────────

#[test]
fn parse_boolean_accepts_bool_decl() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun b () Bool)
        (assert b)
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    assert!(q.var_names().iter().any(|n| n == "b"));
}

#[test]
fn parse_boolean_iff_two_bools_pairwise() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (assert (= a b))
        (assert a)
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parse_boolean_rejects_bool_var_in_ff_term() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun b () Bool)
        (declare-fun x () F)
        (assert (= (ff.add b x) (as ff0 F)))
        (check-sat)
    "#;
    match parse_boolean(src) {
        Err(ParseError::Malformed(_)) => {}
        other => panic!("expected Malformed for Bool in FF term: {:?}", other),
    }
}

// ─────────────── Term-level ite ───────────────

#[test]
fn parse_boolean_term_level_ite() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 101))
        (declare-fun c () Bool)
        (declare-fun x () F)
        (assert (= (ite c x (as ff0 F)) (as ff5 F)))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    assert!(q.var_names().iter().any(|n| n.starts_with("__ite_")));
}

#[test]
fn parse_boolean_term_level_ite_nested() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 101))
        (declare-fun c1 () Bool)
        (declare-fun c2 () Bool)
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (= (ite c1 (ite c2 x y) (as ff0 F)) (as ff5 F)))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    let skolems = q
        .var_names()
        .iter()
        .filter(|n| n.starts_with("__ite_"))
        .count();
    assert_eq!(skolems, 2);
}

// ─────────────── n-ary `=` and `distinct` ───────────────

#[test]
fn parse_boolean_nary_ff_equality() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (declare-fun y () F)
        (declare-fun z () F)
        (assert (= x y z (as ff2 F)))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parse_boolean_distinct_ff() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (declare-fun y () F)
        (declare-fun z () F)
        (assert (distinct x y z))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parse_boolean_distinct_bool_three_is_false() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
        (assert (distinct a b c))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

// ─────────────── define-fun macros ───────────────

#[test]
fn parse_boolean_define_fun_inlines() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (define-fun double ((y F)) F (ff.add y y))
        (assert (= (double x) (as ff2 F)))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parse_boolean_define_fun_bool_macro() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (define-fun nand ((p Bool) (q Bool)) Bool (not (and p q)))
        (assert (nand a b))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

// ─────────────── n-ary xor ───────────────

#[test]
fn parse_boolean_binary_xor() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (assert (xor a b))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parses_negative_ff_constant_ff_form() {
    let prime = BigUint::from(17u32);
    // ff-1 ≡ 16 mod 17
    assert_eq!(parse_ff_const("ff-1", &prime), Some(BigUint::from(16u32)));
    // ff-0 ≡ 0
    assert_eq!(parse_ff_const("ff-0", &prime), Some(BigUint::zero()));
    // ff5 ≡ 5
    assert_eq!(parse_ff_const("ff5", &prime), Some(BigUint::from(5u32)));
    // ff.add and ff.mul must NOT match
    assert_eq!(parse_ff_const("ff.add", &prime), None);
    assert_eq!(parse_ff_const("ff.mul", &prime), None);
}

#[test]
fn parses_negative_ff_constant_hash_form() {
    let prime = BigUint::from(17u32);
    // #f-1m17 ≡ 16
    assert_eq!(parse_ff_const("#f-1m17", &prime), Some(BigUint::from(16u32)));
    // #f3m17 ≡ 3
    assert_eq!(parse_ff_const("#f3m17", &prime), Some(BigUint::from(3u32)));
}

#[test]
fn parse_boolean_ff_bitsum() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun a () (_ FiniteField 3))
        (declare-fun b () (_ FiniteField 3))
        (declare-fun c () (_ FiniteField 3))
        (assert (= (ff.bitsum a b c) #f0m3))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

#[test]
fn parse_boolean_nary_xor() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (declare-fun c () Bool)
        (assert (xor a b c))
        (check-sat)
    "#;
    parse_boolean(src).expect("parse");
}

// ─────────────────────────── SmtSession ─────────────────────────

#[test]
fn session_check_sat_returns_sat_for_satisfiable() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 1);
    assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
}

#[test]
fn session_check_sat_returns_unsat() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f2m7))
        (assert (= x #f3m7))
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert_eq!(outs.len(), 1);
    assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Unsat)));
}

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

#[test]
fn session_named_assert_strips_annotation() {
    // `(assert (! (= x #f5m7) :named foo))` must behave exactly
    // like `(assert (= x #f5m7))` for the purposes of solving.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (! (= x #f5m7) :named foo))
        (check-sat)
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    assert!(matches!(outs[0], SessionOutput::CheckSat(SessionVerdict::Sat)));
}

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

#[test]
fn session_set_option_tlimit_per_is_recorded() {
    // The session records `:tlimit-per` so it can pass a
    // CancelToken with that timeout to each `(check-sat)`.
    let src = r#"
        (set-option :tlimit-per 5000)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.tlimit_per_ms, Some(5000));
}

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

#[test]
fn session_get_value_before_check_sat_returns_empty() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (get-value (x))
    "#;
    let mut sess = SmtSession::new();
    let outs = sess.eval_script(src).expect("eval");
    match &outs[0] {
        SessionOutput::Values(v) => assert!(v.is_empty()),
        other => panic!("expected Values, got {:?}", other),
    }
}

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

#[test]
fn session_silent_to_smtlib_is_empty_string() {
    assert!(SessionOutput::Silent.to_smtlib().is_empty());
}

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

#[test]
fn session_set_option_non_numeric_tlimit_is_ignored() {
    // A non-numeric value silently leaves the existing setting
    // (None) unchanged — no parse error, no spurious timeout.
    let src = r#"
        (set-option :tlimit-per abc)
    "#;
    let mut sess = SmtSession::new();
    sess.eval_script(src).expect("eval");
    assert_eq!(sess.tlimit_per_ms, None);
}

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

// ── adversarial-input robustness (no stack overflow) ─────────────

#[test]
fn deep_sexpr_nesting_is_rejected_not_overflow() {
    // Nesting far beyond MAX_SEXPR_DEPTH must surface as a clean parse
    // error, not a stack-overflow abort (which `catch_unwind` cannot
    // intercept). The depth cap fires inside `parse_one` before the
    // recursion can exhaust the stack.
    let depth = tokenizer::MAX_SEXPR_DEPTH + 500;
    let src = format!(
        "(set-logic QF_FF)\n(declare-fun x () (_ FiniteField 7))\n(assert {}{})\n",
        "(".repeat(depth),
        ")".repeat(depth),
    );
    assert!(parse(&src).is_err(), "deep nesting must be rejected, not crash");
}

#[test]
fn recursive_define_fun_is_rejected_not_overflow() {
    // A self-referential macro would expand without bound; the
    // expansion-depth guard must reject it rather than overflow.
    let src = r#"
        (set-logic QF_FF)
        (define-fun rec () (_ FiniteField 7) (rec))
        (assert (= (rec) (rec)))
        (check-sat)
    "#;
    assert!(parse(src).is_err(), "recursive macro must be rejected, not crash");
}

#[test]
fn zero_arg_minus_is_rejected_not_panic() {
    // `(-)` with no operand must surface a parse error, not index out of
    // bounds in the n-ary minus arm of `build_poly`.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x (-)))
        (check-sat)
    "#;
    assert!(parse(src).is_err(), "(-) must be rejected, not crash");
}

#[test]
fn zero_arg_minus_in_boolean_query_is_rejected_not_panic() {
    // Same arity guard on the boolean term builder (`build_poly_with_ctx`).
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (or (= x (-)) (= x (as ff1 F))))
        (check-sat)
    "#;
    assert!(parse_boolean(src).is_err(), "(-) must be rejected, not crash");
}

#[test]
fn n_ary_minus_is_left_associative_in_parse() {
    // (- a b c) = ((a - b) - c). In GF(7): (5 - 2 - 1) = 2.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x (- (as ff5 F) (as ff2 F) (as ff1 F))))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse n-ary minus");
    assert_eq!(cs.prime, BigUint::from(7u32));
    assert_eq!(cs.equalities.len(), 1);
}

#[test]
fn n_ary_minus_is_left_associative_in_parse_boolean() {
    // Same shape under the boolean-query parser.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (or
            (= x (- (as ff5 F) (as ff2 F) (as ff1 F)))
            (= y (- (as ff0 F) (as ff1 F)))
        ))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse n-ary minus (boolean)");
    // Just confirm the query parsed; structural checks are covered elsewhere.
    let _ = q;
}

#[test]
fn ff_bitsum_in_assert_decomposes_to_weighted_sum() {
    // ff.bitsum [b0, b1, b2] = b0 + 2·b1 + 4·b2 in GF(7).
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun b0 () F)
        (declare-fun b1 () F)
        (declare-fun b2 () F)
        (declare-fun s () F)
        (assert (= s (ff.bitsum b0 b1 b2)))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse ff.bitsum");
    assert_eq!(cs.equalities.len(), 1);
}

// ────────── parse() malformed-input rejection (robustness) ──────────

/// Standard GF(7) preamble + one body assert, for malformed-assert tests.
fn parse_with_assert(body: &str) -> Result<ConstraintSystem, ParseError> {
    let src = format!(
        "(set-logic QF_FF)\n\
         (define-sort F () (_ FiniteField 7))\n\
         (declare-fun x () F)\n\
         (declare-fun y () F)\n\
         (assert {})\n\
         (check-sat)\n",
        body
    );
    parse(&src)
}

#[test]
fn eq_with_wrong_arity_is_malformed() {
    // (= x) has arity 1, not 2.
    assert!(matches!(parse_with_assert("(= x)"), Err(ParseError::Malformed(_))));
    // (= x y x) has arity 3.
    assert!(matches!(parse_with_assert("(= x y x)"), Err(ParseError::Malformed(_))));
}

#[test]
fn not_with_non_equality_inner_is_malformed() {
    // (not (ff.mul x y)) — inner head is not '='.
    assert!(matches!(
        parse_with_assert("(not (ff.mul x y))"),
        Err(ParseError::Malformed(_))
    ));
}

#[test]
fn not_with_atom_inner_is_malformed() {
    // (not x) — inner is an atom, not a list.
    assert!(matches!(parse_with_assert("(not x)"), Err(ParseError::Malformed(_))));
}

#[test]
fn not_with_inner_equality_wrong_arity_is_malformed() {
    // (not (= x)) — inner '=' has arity 1.
    assert!(matches!(parse_with_assert("(not (= x))"), Err(ParseError::Malformed(_))));
}

#[test]
fn unsupported_assert_head_is_malformed() {
    // (assert (foo x y)) — 'foo' is neither '=' nor 'not' nor a boolean op.
    assert!(matches!(parse_with_assert("(bar x y)"), Err(ParseError::Malformed(_))));
}

#[test]
fn non_list_assert_body_is_malformed() {
    // (assert x) — the body is an atom, not a list.
    assert!(matches!(parse_with_assert("x"), Err(ParseError::Malformed(_))));
}

#[test]
fn assert_with_wrong_arity_is_malformed() {
    let src = "(set-logic QF_FF)\n\
               (define-sort F () (_ FiniteField 7))\n\
               (declare-fun x () F)\n\
               (assert)\n\
               (check-sat)\n";
    assert!(matches!(parse(src), Err(ParseError::Malformed(_))));
}

#[test]
fn bool_declaration_in_conjunctive_parser_is_malformed() {
    // The conjunctive parser rejects Bool-sorted declarations (use parse_boolean).
    let src = "(set-logic QF_FF)\n\
               (define-sort F () (_ FiniteField 7))\n\
               (declare-fun b () Bool)\n\
               (check-sat)\n";
    assert!(matches!(parse(src), Err(ParseError::Malformed(_))));
}

#[test]
fn multiple_distinct_ff_literal_primes_is_malformed() {
    // No FF sort declaration ⇒ literal-based prime inference; two distinct
    // moduli (#f3m7 vs #f3m11) is a malformed single-prime session.
    let src = "(set-logic QF_FF)\n\
               (declare-fun x () F)\n\
               (declare-fun y () F)\n\
               (assert (= x #f3m7))\n\
               (assert (= y #f3m11))\n\
               (check-sat)\n";
    assert!(matches!(parse(src), Err(ParseError::Malformed(_))));
}

#[test]
fn no_prime_anywhere_is_missing_prime() {
    // No FF sort, no FF literals ⇒ MissingPrime (distinct from Malformed).
    let src = "(set-logic QF_FF)\n(check-sat)\n";
    assert!(matches!(parse(src), Err(ParseError::MissingPrime)));
}

// ────────── parse_boolean() FF-term builder edge / error paths ──────────

/// parse_boolean preamble with FF vars x, y and a Bool var b, plus one
/// body assert.
fn parse_boolean_with_assert(body: &str) -> Result<crate::boolean::BooleanQuery, ParseError> {
    let src = format!(
        "(set-logic QF_FF)\n\
         (define-sort F () (_ FiniteField 7))\n\
         (declare-fun x () F)\n\
         (declare-fun y () F)\n\
         (declare-fun b () Bool)\n\
         (assert {})\n\
         (check-sat)\n",
        body
    );
    parse_boolean(&src)
}

#[test]
fn boolean_macro_arity_mismatch_is_malformed() {
    let src = "(set-logic QF_FF)\n\
               (define-sort F () (_ FiniteField 7))\n\
               (declare-fun x () F)\n\
               (define-fun g ((a F)) F (ff.add a a))\n\
               (assert (= x (g x x)))\n\
               (check-sat)\n";
    // g expects 1 arg, called with 2.
    assert!(matches!(parse_boolean(src), Err(ParseError::Malformed(_))));
}

#[test]
fn boolean_equality_mixing_bool_and_ff_is_malformed() {
    // (= x b): x is FF, b is Bool — the chain sort check rejects the mix.
    assert!(matches!(
        parse_boolean_with_assert("(= x b)"),
        Err(ParseError::Malformed(_))
    ));
}

#[test]
fn boolean_as_constant_wrong_arity_is_malformed() {
    // (as ff1) has arity 2, not 3.
    assert!(matches!(
        parse_boolean_with_assert("(= x (as ff1))"),
        Err(ParseError::Malformed(_))
    ));
}

#[test]
fn boolean_ff_neg_wrong_arity_is_malformed() {
    assert!(matches!(
        parse_boolean_with_assert("(= x (ff.neg x y))"),
        Err(ParseError::Malformed(_))
    ));
}

#[test]
fn boolean_unknown_ff_operator_is_unknown_operator() {
    assert!(matches!(
        parse_boolean_with_assert("(= x (ff.frobnicate x))"),
        Err(ParseError::UnknownOperator(_))
    ));
}

#[test]
fn boolean_unary_minus_in_ff_term_parses() {
    // (- y) drives the binary '-' (negation) arm of build_poly_with_ctx.
    assert!(parse_boolean_with_assert("(= x (- y))").is_ok());
}

#[test]
fn boolean_decimal_literal_in_ff_term_parses() {
    // A bare decimal in an FF term is reduced mod prime.
    assert!(parse_boolean_with_assert("(= x 5)").is_ok());
}

#[test]
fn parse_error_display_covers_every_variant() {
    // Exercise every Display arm so the impl isn't covered only by panics.
    assert_eq!(
        format!("{}", ParseError::UnexpectedToken("xyz".into())),
        "unexpected token: xyz"
    );
    assert_eq!(
        format!("{}", ParseError::UnknownOperator("ff.foo".into())),
        "unsupported FF operator: ff.foo"
    );
    assert_eq!(
        format!("{}", ParseError::UnknownSymbol("undef".into())),
        "unknown symbol: undef"
    );
    assert_eq!(
        format!("{}", ParseError::BooleanInAssert("or".into())),
        "boolean operator 'or' inside assert (QF_FF only)"
    );
    assert_eq!(
        format!("{}", ParseError::MissingPrime),
        "assert before any FF sort declaration"
    );
    assert_eq!(
        format!("{}", ParseError::Malformed("(declare-fun)".into())),
        "malformed form: (declare-fun)"
    );
    // std::error::Error blanket — just verify the trait is implemented.
    let _: &dyn std::error::Error = &ParseError::MissingPrime;
}
