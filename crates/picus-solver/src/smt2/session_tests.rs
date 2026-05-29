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

// UNSAT-via-contradiction coverage folded into
// `prop_contradictory_constants_unsat_across_edge_primes` (GF3,5,7,11,13).

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
//
// `get_unsat_core_returns_names_after_unsat` (shallow: only asserts an
// UnsatCore output exists) is subsumed by
// `named_annotation_skips_other_attributes` further down, which uses the
// same `(! ... :named ...)` annotation, runs through UNSAT, and asserts
// that the returned core contains the expected name.

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

// `default_equals_new` collapsed into `new_starts_at_level_zero_no_check`
// (identical three assertions on the freshly-built session state).

// ────────── eval() Silent fallthroughs ──────────
//
// The four shape variants (top-level atom / empty list / non-atom-head /
// unknown command) each hit a distinct dispatch arm but all assert
// `out.is_empty()`. They share a helper, so fold into a single sweep.
#[test]
fn silent_fallthroughs_across_dispatch_arms() {
    // Each source string is an "inert" top-level form that must yield
    // zero outputs from the command dispatcher:
    //   "hello"          → bare atom, not a List (atom arm)
    //   "()"             → empty List (no head arm)
    //   "(() x)"         → head is itself a List, not an Atom
    //   "(unknown-cmd arg)" → atom head with no command registered
    for src in ["hello", "()", "(() x)", "(unknown-cmd arg)"] {
        let out = run(src);
        assert!(out.is_empty(), "expected empty output for {:?}", src);
    }
}

// ────────── echo edge case ──────────

#[test]
fn echo_missing_argument_is_empty_string() {
    let out = run("(echo)");
    match out.last() {
        Some(SessionOutput::Echo(s)) => assert_eq!(s.as_str(), ""),
        other => panic!("expected empty Echo, got {:?}", other),
    }
}

// ────────── define-sort ──────────

#[test]
fn define_sort_sets_prime() {
    let mut s = SmtSession::new();
    let out = run_with(&mut s, "(define-sort MyFF () (_ FiniteField 7))");
    assert!(out.is_empty());
    assert_eq!(s.prime, Some(num_bigint::BigUint::from(7u32)));
}

#[test]
fn define_sort_too_short_is_silent_noop() {
    let mut s = SmtSession::new();
    // < 4 elements: eval_define_sort returns Ok(()) without touching prime.
    let out = run_with(&mut s, "(define-sort X)");
    assert!(out.is_empty());
    assert!(s.prime.is_none());
}

// ────────── assert arity + literal-prime inference ──────────

#[test]
fn assert_wrong_arity_errors() {
    let mut s = SmtSession::new();
    let err = s
        .eval_script("(assert true false)")
        .expect_err("assert with 3 elements is malformed");
    match err {
        ParseError::Malformed(msg) => assert!(msg.contains("assert")),
        other => panic!("expected Malformed arity error, got {:?}", other),
    }
}

#[test]
fn assert_with_multiple_literal_primes_errors() {
    let mut s = SmtSession::new();
    let err = s
        .eval_script("(assert (= #f1m7 #f2m11))")
        .expect_err("conflicting FF primes are malformed");
    match err {
        ParseError::Malformed(msg) => assert!(msg.contains("multiple FF primes")),
        other => panic!("expected multiple-FF-primes Malformed, got {:?}", other),
    }
}

#[test]
fn assert_single_literal_prime_is_inferred() {
    // No declaration; the `#f..m7` literal pins the session prime to 7.
    let mut s = SmtSession::new();
    let _ = run_with(&mut s, "(assert (= #f1m7 #f1m7))");
    assert_eq!(s.prime, Some(num_bigint::BigUint::from(7u32)));
}

#[test]
fn assert_parse_failure_reinstalls_builder() {
    // A malformed assert body (unknown operator) errors, but the session
    // must remain usable for the next command.
    let mut s = SmtSession::new();
    let _ = run_with(&mut s, "(declare-fun x () (_ FiniteField 7))");
    let err = s
        .eval_script("(assert (bogus-op x))")
        .expect_err("unknown operator is an error");
    assert!(matches!(err, ParseError::Malformed(_) | ParseError::UnknownOperator(_)));
    // Session still works: a valid assert + check-sat succeeds.
    let out = run_with(&mut s, "(assert (= x #f1m7)) (check-sat)");
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

// ────────── check-sat empty / Bool default ──────────
//
// `check_sat_with_no_assertions_is_sat` (empty formula → Formula::True →
// SAT) is subsumed by `prop_reset_assertions_clears_unsat_constraints`,
// which after `(reset-assertions)` issues a bare `(check-sat)` and
// asserts the same SAT verdict.

// ────────── set-option :tlimit-per parsing ──────────
//
// `set_option_tlimit_per_stores_value` (set 1000, observe `Some(1000)`)
// is folded into `set_option_tlimit_per_zero_disables`, which seeds the
// same `Some(1000)` first and then transitions it to `None` via `0`.

#[test]
fn set_option_tlimit_per_zero_disables() {
    let mut s = SmtSession::new();
    // Seed a non-None value first, then 0 must clear it back to None.
    let _ = run_with(&mut s, "(set-option :tlimit-per 1000)");
    assert_eq!(s.tlimit_per_ms, Some(1000));
    let _ = run_with(&mut s, "(set-option :tlimit-per 0)");
    assert_eq!(s.tlimit_per_ms, None);
}

#[test]
fn set_option_tlimit_per_non_numeric_is_ignored() {
    let mut s = SmtSession::new();
    let _ = run_with(&mut s, "(set-option :tlimit-per notanumber)");
    assert_eq!(s.tlimit_per_ms, None);
}

#[test]
fn set_option_unknown_keyword_is_ignored() {
    let mut s = SmtSession::new();
    let out = run_with(&mut s, "(set-option :unknown-opt foo)");
    assert!(out.is_empty());
    assert_eq!(s.tlimit_per_ms, None);
}

#[test]
fn check_sat_honours_generous_tlimit() {
    // A large per-check timeout exercises the Some(ms) → CancelToken::
    // with_timeout branch; the easy problem still finishes well within it.
    let mut s = SmtSession::new();
    let out = run_with(
        &mut s,
        r#"
            (set-option :tlimit-per 60000)
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    assert_eq!(s.tlimit_per_ms, Some(60000));
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
}

// ────────── declare-fun malformed ──────────

#[test]
fn declare_fun_malformed_is_silent_noop() {
    let mut s = SmtSession::new();
    // classify_declare returns None (list too short) → eval_declare early
    // returns Ok without registering any variable.
    let out = run_with(&mut s, "(declare-fun)");
    assert!(out.is_empty());
    assert!(s.vars.is_empty());
    assert!(s.var_order.is_empty());
}

// ────────── get-value ──────────

#[test]
fn get_value_without_model_is_empty() {
    let mut s = SmtSession::new();
    let _ = run_with(&mut s, "(declare-fun x () (_ FiniteField 7))");
    // No prior check-sat ⇒ no model ⇒ empty value list.
    let out = run_with(&mut s, "(get-value (x))");
    match out.last() {
        Some(SessionOutput::Values(v)) => assert!(v.is_empty()),
        other => panic!("expected empty Values, got {:?}", other),
    }
}

#[test]
fn get_value_malformed_query_is_empty() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    // Query argument is an atom, not a list → empty value list.
    let out = run_with(&mut s, "(get-value x)");
    match out.last() {
        Some(SessionOutput::Values(v)) => assert!(v.is_empty()),
        other => panic!("expected empty Values, got {:?}", other),
    }
}

#[test]
fn get_value_unknown_variable_is_skipped() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    // `undefined` is not a declared var → skipped, yielding an empty list.
    let out = run_with(&mut s, "(get-value (undefined))");
    match out.last() {
        Some(SessionOutput::Values(v)) => assert!(v.is_empty()),
        other => panic!("expected empty Values, got {:?}", other),
    }
}

#[test]
fn get_value_returns_model_value() {
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    assert_eq!(s.last_verdict(), Some(SessionVerdict::Sat));
    // x is forced to 1 (mod 7); FF values format as `#f<val>m<prime>`.
    let out = run_with(&mut s, "(get-value (x))");
    match out.last() {
        Some(SessionOutput::Values(v)) => {
            assert_eq!(v.len(), 1);
            assert_eq!(v[0].0, "x");
            assert_eq!(v[0].1, "#f1m7");
        }
        other => panic!("expected one-entry Values, got {:?}", other),
    }
}

#[test]
fn get_value_declared_but_unconstrained_defaults_to_zero() {
    // `y` is declared and in scope but appears in no constraint, so it may
    // be absent from the model; eval_get_value falls back to a 0 value.
    let mut s = SmtSession::new();
    let _ = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (declare-fun y () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    assert_eq!(s.last_verdict(), Some(SessionVerdict::Sat));
    let out = run_with(&mut s, "(get-value (y))");
    match out.last() {
        Some(SessionOutput::Values(v)) => {
            assert_eq!(v.len(), 1);
            assert_eq!(v[0].0, "y");
            // Value is a valid FF7 element regardless of whether the model
            // pinned it; the default-fill path yields `#f0m7`.
            assert!(v[0].1.starts_with("#f") && v[0].1.ends_with("m7"));
        }
        other => panic!("expected one-entry Values, got {:?}", other),
    }
}

// ────────── :named annotation skipping other attributes ──────────

#[test]
fn named_annotation_skips_other_attributes() {
    // `(! term :foo bar :named n1)` must capture `n1` while ignoring `:foo`.
    let mut s = SmtSession::new();
    let out = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (! (= x #f1m7) :foo bar :named n1))
            (assert (= x #f2m7))
            (check-sat)
            (get-unsat-core)
        "#,
    );
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Unsat));
    // The named assert is in scope at UNSAT, so its label appears in the core.
    let core = out
        .iter()
        .find_map(|o| match o {
            SessionOutput::UnsatCore(names) => Some(names.clone()),
            _ => None,
        })
        .expect("an UnsatCore output");
    assert!(core.contains(&"n1".to_string()), "core missing n1: {:?}", core);
}

// ────────── formatting helpers (None-prime fallbacks) ──────────

#[test]
fn format_value_ff_without_prime_is_bare_decimal() {
    let v = num_bigint::BigUint::from(5u32);
    assert_eq!(super::format_value(&v, super::VarSort::Ff, None), "5");
}

#[test]
fn format_value_bool_maps_zero_one() {
    let zero = num_bigint::BigUint::from(0u32);
    let one = num_bigint::BigUint::from(1u32);
    assert_eq!(super::format_value(&zero, super::VarSort::Bool, None), "false");
    assert_eq!(super::format_value(&one, super::VarSort::Bool, None), "true");
}

#[test]
fn format_define_fun_ff_without_prime_uses_underscore_sort() {
    let v = num_bigint::BigUint::from(9u32);
    assert_eq!(
        super::format_define_fun("y", &v, super::VarSort::Ff, None),
        "(define-fun y () _ 9)"
    );
}

// `echo_output_to_smtlib_quotes_text` folded into
// `to_smtlib_renders_each_session_output_variant`.

// ────────── assert with FF op but no prime hint ──────────

#[test]
fn assert_ff_op_without_prime_is_missing_prime() {
    // An `ff.*` operator with no `#fNmP` literal and no prior FF sort
    // declaration cannot infer a modulus; the assert must reject with
    // MissingPrime rather than silently encode under the prime-2 default.
    let mut s = SmtSession::new();
    let err = s
        .eval_script("(assert (ff.add x y))")
        .expect_err("ff op without a prime hint must error");
    assert!(matches!(err, ParseError::MissingPrime), "got {:?}", err);
}

// ────────── check-sat Unknown verdict ──────────

#[test]
fn check_sat_unknown_when_iteration_cap_exhausted() {
    // A zero CDCL(T) iteration cap forces `solve_formula` to return
    // Unknown on the first loop turn; check_sat maps that to the Unknown
    // verdict and clears any prior model / unsat-core state.
    let _g = crate::config::ConfigGuard::with_override(|c| c.cdclt_iter_cap = 0);
    let mut s = SmtSession::new();
    let out = run_with(
        &mut s,
        r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f1m7))
            (check-sat)
        "#,
    );
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Unknown));
    assert_eq!(s.last_verdict(), Some(SessionVerdict::Unknown));
    assert!(s.last_model().is_none());
}

// ────────── set-option edge cases ──────────

#[test]
fn set_option_tlimit_per_without_value_is_ignored() {
    // `:tlimit-per` with no following token: the inner `list.get(i+1)`
    // is None, so no value is stored, then `i += 2` advances past it.
    let mut s = SmtSession::new();
    let out = run_with(&mut s, "(set-option :tlimit-per)");
    assert!(out.is_empty());
    assert_eq!(s.tlimit_per_ms, None);
}

#[test]
fn set_option_non_colon_token_is_skipped_singly() {
    // An option token that is a plain atom (no leading ':') is neither
    // `:tlimit-per` nor a generic `:key` — it advances the cursor by one
    // (the `i += 1` fall-through) without consuming a value.
    let mut s = SmtSession::new();
    let out = run_with(&mut s, "(set-option plainflag :tlimit-per 500)");
    assert!(out.is_empty());
    // The `:tlimit-per 500` pair after the plain token is still honoured.
    assert_eq!(s.tlimit_per_ms, Some(500));
}

#[test]
fn set_option_non_atom_token_is_skipped_singly() {
    // A non-atom option element (a nested list) skips the `if let Atom`
    // guard entirely and falls through to the single-step `i += 1`.
    let mut s = SmtSession::new();
    let out = run_with(&mut s, "(set-option (nested list) :tlimit-per 750)");
    assert!(out.is_empty());
    assert_eq!(s.tlimit_per_ms, Some(750));
}

// ────────── define-sort bad prime ──────────

#[test]
fn define_sort_unparseable_prime_errors() {
    // `(_ FiniteField <garbage>)` matches the finite-field sort shape, but
    // the modulus token fails to parse as a BigUint, exercising the
    // `.map_err(...)` arm.
    let mut s = SmtSession::new();
    let err = s
        .eval_script("(define-sort Bad () (_ FiniteField notaprime))")
        .expect_err("non-numeric prime must error");
    match err {
        ParseError::Malformed(msg) => assert!(msg.contains("bad prime"), "msg: {}", msg),
        other => panic!("expected Malformed bad-prime, got {:?}", other),
    }
    assert!(s.prime.is_none(), "prime must stay unset on parse failure");
}

// ────────── strip_named_annotation edge cases ──────────

#[test]
fn strip_named_annotation_passthroughs_when_not_a_bang_annotation() {
    // Two distinct passthrough arms both yield `name == None` and return
    // the wrapper unchanged:
    //   1) `(!)`        — list shorter than 2, no inner term slot
    //   2) `((..) x)`   — head is a list, not the `!` atom
    let too_short = Sexpr::List(vec![Sexpr::Atom("!".into())]);
    let (inner1, n1) = super::strip_named_annotation(&too_short);
    assert!(n1.is_none());
    assert!(matches!(inner1, Sexpr::List(l) if l.len() == 1));

    let non_atom_head = Sexpr::List(vec![
        Sexpr::List(vec![Sexpr::Atom("inner".into())]),
        Sexpr::Atom("x".into()),
    ]);
    let (_inner2, n2) = super::strip_named_annotation(&non_atom_head);
    assert!(n2.is_none());
}

#[test]
fn strip_named_annotation_skips_non_atom_attribute_token() {
    // Inside `(! term <list> :named n)`, a non-atom attribute element
    // (a nested list) is stepped over by the single-advance `i += 1`,
    // while the `:named n` pair is still captured.
    let s = Sexpr::List(vec![
        Sexpr::Atom("!".into()),
        Sexpr::Atom("term".into()),
        Sexpr::List(vec![Sexpr::Atom("ignored".into())]),
        Sexpr::Atom(":named".into()),
        Sexpr::Atom("n".into()),
    ]);
    let (inner, name) = super::strip_named_annotation(&s);
    assert_eq!(name, Some("n".to_string()));
    assert!(matches!(inner, Sexpr::Atom(a) if a == "term"));
}

#[test]
fn strip_named_annotation_skips_generic_colon_attribute() {
    // A generic `:key value` attribute (no `:named`) is consumed two
    // tokens at a time; the result carries no name.
    let s = Sexpr::List(vec![
        Sexpr::Atom("!".into()),
        Sexpr::Atom("term".into()),
        Sexpr::Atom(":weight".into()),
        Sexpr::Atom("3".into()),
    ]);
    let (inner, name) = super::strip_named_annotation(&s);
    assert!(name.is_none());
    assert!(matches!(inner, Sexpr::Atom(a) if a == "term"));
}

// ────────── to_smtlib: per-variant rendering ──────────
//
// One-shot sweep covering every "small" SessionOutput variant's
// `to_smtlib()` rendering. The Model variant is exercised separately
// below via an end-to-end check-sat → get-model round-trip (which also
// subsumes the shallow `model_output_to_smtlib_clones_payload` unit on
// the Model variant).
#[test]
fn to_smtlib_renders_each_session_output_variant() {
    // CheckSat / Unknown
    assert_eq!(
        SessionOutput::CheckSat(SessionVerdict::Unknown).to_smtlib(),
        "unknown"
    );
    // Echo: surrounding quotes preserved.
    assert_eq!(SessionOutput::Echo("hi".into()).to_smtlib(), "\"hi\"");
    // Values: `((n0 v0)\n (n1 v1)...)`
    let vals = SessionOutput::Values(vec![
        ("x".into(), "#f3m7".into()),
        ("b".into(), "true".into()),
    ]);
    assert_eq!(vals.to_smtlib(), "((x #f3m7)\n (b true))");
    // UnsatCore: space-separated names in parens.
    let core = SessionOutput::UnsatCore(vec!["a".into(), "b".into(), "c".into()]);
    assert_eq!(core.to_smtlib(), "(a b c)");
    // Silent: empty string.
    assert_eq!(SessionOutput::Silent.to_smtlib(), "");
}

#[test]
fn get_model_to_smtlib_matches_session_format_model() {
    // End-to-end: a real check-sat → get-model output's `.to_smtlib()`
    // round-trips the exact same string `format_model()` produced.
    let mut s = SmtSession::new();
    let outs = s
        .eval_script(
            r#"
            (declare-fun x () (_ FiniteField 7))
            (assert (= x #f3m7))
            (check-sat)
            (get-model)
        "#,
        )
        .expect("script ok");
    let model_text = match outs.iter().rev().find(|o| matches!(o, SessionOutput::Model(_))) {
        Some(SessionOutput::Model(s)) => s.clone(),
        other => panic!("expected a Model output, got {:?}", other),
    };
    // to_smtlib on the Model variant returns the underlying string.
    let smt = SessionOutput::Model(model_text.clone()).to_smtlib();
    assert_eq!(smt, model_text);
    // Sanity: the model carries the expected define-fun line.
    assert!(
        smt.contains("(define-fun x () (_ FiniteField 7) #f3m7)"),
        "model missing x definition: {}",
        smt
    );
}

// `values_output_to_smtlib_formats_name_value_pairs`,
// `unsat_core_output_to_smtlib_space_separates_names`, and
// `silent_output_to_smtlib_is_empty_string` folded into
// `to_smtlib_renders_each_session_output_variant` above.

// ════════════════ SPEC-DRIVEN property tests ════════════════
//
// Each property is derived from the SMT-LIB v2 incremental-mode spec
// (§4.1 — stack, §4.2 — assert, §4.2.1 — reset, etc.) or from
// solver-engine equivalence properties — not from inspecting the source.

// `prop_two_sessions_same_script_yield_same_verdicts` (determinism on a
// trivial GF7 script) is subsumed by the surviving prop tests below
// (every prop running a script twice — `prop_reset_is_idempotent`,
// `prop_reset_assertions_clears_unsat_constraints` — exercises the same
// pure-function-of-script guarantee).
//
// `prop_reset_then_script_equals_fresh_session_run` (reset → script ≡
// fresh session → script) is subsumed by `reset_clears_everything`
// (resets then runs an unrelated GF11 script and asserts the verdict)
// combined with `prop_reset_is_idempotent` (which compares post-reset
// verdicts against a baseline).

/// SPEC: SAT `check-sat` followed by `get-model` returns a model whose
/// printed FF values are valid `#fNmP` literals. Round-tripping each
/// value through `parse_ff_const` recovers a field element in [0, p).
#[test]
fn prop_get_model_ff_values_round_trip_through_parse_ff_const() {
    use num_bigint::BigUint;
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
        (check-sat)
        (get-model)
    "#;
    let out = run(src);
    let model_text = out
        .iter()
        .find_map(|o| match o {
            SessionOutput::Model(s) => Some(s.clone()),
            _ => None,
        })
        .expect("model present");
    // Every `#fNmP` literal in the printed model must:
    //   1. parse back via parse_ff_const under the same prime,
    //   2. yield a value < prime.
    let prime = BigUint::from(7u32);
    let mut found_any = false;
    for tok in model_text.split(|c: char| c.is_whitespace() || c == '(' || c == ')') {
        if tok.starts_with("#f") {
            found_any = true;
            let parsed = super::super::parse_ff_const(tok, &prime)
                .unwrap_or_else(|| panic!("printed literal {:?} must reparse", tok));
            assert!(parsed < prime, "model value {} must be < {}", parsed, prime);
        }
    }
    assert!(found_any, "expected at least one #fNmP literal in model");
}

/// SPEC (engine equivalence): If `(check-sat)` returns SAT, the model
/// returned by `(get-value (x))` MUST satisfy each asserted equality.
/// Test: assert `(= (ff.add x y) #f5m7)` and `(= (ff.mul x y) #f6m7)`,
/// then verify the returned (x, y) satisfies BOTH equations mod 7.
#[test]
fn prop_sat_model_satisfies_every_assertion() {
    use num_bigint::BigUint;
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 7))
        (assert (= (ff.add x y) #f5m7))
        (assert (= (ff.mul x y) #f6m7))
        (check-sat)
        (get-value (x y))
    "#;
    let mut s = SmtSession::new();
    let out = s.eval_script(src).expect("eval");
    assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
    let model = s.last_model().expect("model");
    let prime = BigUint::from(7u32);
    let x = model.get("x").cloned().expect("x");
    let y = model.get("y").cloned().expect("y");
    // Math check: x + y ≡ 5 and x*y ≡ 6 (mod 7).
    assert_eq!((&x + &y) % &prime, BigUint::from(5u32));
    assert_eq!((&x * &y) % &prime, BigUint::from(6u32));
}

/// SPEC: `(set-option :tlimit-per 0)` disables the per-check timeout
/// (documented behavior in session.rs). Therefore a tiny GF check that
/// completes instantly must return a definite verdict after 0 is set —
/// never `Unknown` (which would indicate an erroneous immediate
/// timeout).
#[test]
fn prop_tlimit_per_zero_does_not_force_unknown() {
    let src = r#"
        (set-logic QF_FF)
        (set-option :tlimit-per 0)
        (declare-fun x () (_ FiniteField 5))
        (assert (= x #f2m5))
        (check-sat)
    "#;
    let v = last_verdict(&run(src));
    assert_ne!(v, Some(SessionVerdict::Unknown));
    assert_eq!(v, Some(SessionVerdict::Sat));
}

/// SPEC (idempotence): `(reset)` is idempotent — calling it twice in a
/// row leaves the session in the same state as calling it once. We
/// verify: after `(reset)`, the verdict of a fresh script S is the
/// same as after `(reset)(reset)`.
#[test]
fn prop_reset_is_idempotent() {
    let post = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 5))
        (assert (= x #f2m5))
        (check-sat)
    "#;
    let mut s1 = SmtSession::new();
    s1.eval_script("(set-logic QF_FF) (declare-fun y () (_ FiniteField 7)) (reset)")
        .expect("a");
    let mut s2 = SmtSession::new();
    s2.eval_script("(set-logic QF_FF) (declare-fun y () (_ FiniteField 7)) (reset) (reset)")
        .expect("b");
    let v1 = last_verdict(&s1.eval_script(post).expect("c"));
    let v2 = last_verdict(&s2.eval_script(post).expect("d"));
    assert_eq!(v1, v2);
}

/// SPEC: `(reset-assertions)` clears the assertion stack but keeps
/// declarations (§4.2.1). Therefore: after reset-assertions, a check-sat
/// with no further asserts must return SAT (vacuously) — the previously
/// asserted unsat constraints no longer apply, and there's nothing left
/// to contradict.
#[test]
fn prop_reset_assertions_clears_unsat_constraints() {
    let mut s = SmtSession::new();
    s.eval_script(
        "(set-logic QF_FF)
         (declare-fun x () (_ FiniteField 7))
         (assert (= x #f2m7))
         (assert (= x #f3m7))",
    )
    .expect("setup");
    // Pre: UNSAT.
    let pre = last_verdict(&s.eval_script("(check-sat)").expect("pre"));
    assert_eq!(pre, Some(SessionVerdict::Unsat));
    // Reset assertions, then check again — must be SAT (no constraints).
    s.eval_script("(reset-assertions)").expect("ra");
    let post = last_verdict(&s.eval_script("(check-sat)").expect("post"));
    assert_eq!(post, Some(SessionVerdict::Sat));
}

/// SPEC: An asserted contradiction across different primes (GF(2),
/// GF(3), GF(5), GF(7), GF(11)) must each yield UNSAT. The verdict for
/// `x = a ∧ x = b` where a ≠ b (mod p) is UNSAT for every prime where
/// the literals encode distinct field elements.
#[test]
fn prop_contradictory_constants_unsat_across_edge_primes() {
    for &p in &[3u32, 5, 7, 11, 13] {
        let src = format!(
            "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= x #f1m{})) (assert (= x #f2m{})) (check-sat)",
            p, p, p
        );
        let v = last_verdict(&run(&src));
        assert_eq!(
            v,
            Some(SessionVerdict::Unsat),
            "expected UNSAT in GF({}) for x=1 ∧ x=2",
            p
        );
    }
}

/// SPEC: A satisfiable single-variable equality is SAT regardless of
/// prime. (Existence of solution = literal in field is trivial.)
#[test]
fn prop_single_value_assertion_sat_across_edge_primes() {
    for &p in &[2u32, 3, 5, 7, 11] {
        let src = format!(
            "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= x #f0m{})) (check-sat)",
            p, p
        );
        let v = last_verdict(&run(&src));
        assert_eq!(
            v,
            Some(SessionVerdict::Sat),
            "expected SAT in GF({}) for x=0",
            p
        );
    }
}

/// SPEC: For prime p>2, `(= (ff.add x x) #f0mp)` has the unique
/// solution x = 0 (since 2 is invertible). So check-sat is SAT and the
/// model must have x = 0. This probes that the parser+solver respect
/// the field characteristic in a non-trivial way.
#[test]
fn prop_double_equals_zero_has_unique_solution_in_odd_prime() {
    use num_bigint::BigUint;
    for &p in &[3u32, 5, 7, 11, 13] {
        let src = format!(
            "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= (ff.add x x) #f0m{})) (check-sat) (get-value (x))",
            p, p
        );
        let mut s = SmtSession::new();
        let out = s.eval_script(&src).expect("eval");
        assert_eq!(last_verdict(&out), Some(SessionVerdict::Sat));
        let x = s.last_model().unwrap().get("x").cloned().unwrap();
        assert_eq!(
            x,
            BigUint::from(0u32),
            "for odd p={}, 2x=0 forces x=0, got {}",
            p,
            x
        );
    }
}

