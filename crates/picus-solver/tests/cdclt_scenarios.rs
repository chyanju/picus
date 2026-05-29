//! CDCL(T) SAT-model-content coverage: on SAT, `solve_formula` returns a
//! model that includes the expected FF / Boolean / ITE variables with the
//! correct values. (Verdict parity between the CDCL(T) and DNF paths lives
//! in `cdclt_vs_dnf_parity.rs`.)

use num_bigint::BigUint;
use picus_solver::cdclt::solve_formula;
use picus_solver::core::SolveOutcome;
use picus_solver::smt2::parse_boolean;
use picus_core::timeout::CancelToken;

// ─────────────────── SAT model contents ────────────────────────────

/// CDCL(T) SAT must return a model that includes the FF variable.
#[test]
fn cdclt_sat_model_includes_ff_var() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(assert (= x #f3m7))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)),
                "x must be present and equal to 3; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// CDCL(T) SAT must return a model that includes any Bool variable
/// that appeared on the trail. Bool vars are encoded as FF elements
/// in {0, 1}, so the model entry is a `BigUint` of 0 or 1.
#[test]
fn cdclt_sat_model_includes_bool_var_true() {
    let src = r#"
(set-logic QF_FF)
(declare-fun b () Bool)
(assert b)
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b"), Some(&BigUint::from(1u32)),
                "b asserted ⇒ model must have b = 1; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

#[test]
fn cdclt_sat_model_includes_bool_var_false() {
    let src = r#"
(set-logic QF_FF)
(declare-fun b () Bool)
(assert (not b))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("b"), Some(&BigUint::from(0u32)),
                "¬b asserted ⇒ model must have b = 0; got {:?}", m);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Free Bool variable (no constraint on it): the model must still
/// include it, with value in {0, 1}.
#[test]
fn cdclt_sat_model_includes_free_bool_var() {
    let src = r#"
(set-logic QF_FF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let a_val = m.get("a").expect("a in model").clone();
            let b_val = m.get("b").expect("b in model").clone();
            assert!(a_val == BigUint::from(0u32) || a_val == BigUint::from(1u32),
                "a must be 0 or 1, got {:?}", a_val);
            assert!(b_val == BigUint::from(0u32) || b_val == BigUint::from(1u32),
                "b must be 0 or 1, got {:?}", b_val);
            assert!(a_val == BigUint::from(1u32) || b_val == BigUint::from(1u32),
                "(or a b) ⇒ at least one is 1; got a={:?} b={:?}", a_val, b_val);
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Mixed Bool + FF SAT: both must be present in the model.
#[test]
fn cdclt_sat_model_includes_mixed_bool_and_ff() {
    let src = r#"
(set-logic QF_FF)
(declare-fun x () (_ FiniteField 7))
(declare-fun b () Bool)
(assert b)
(assert (= x #f3m7))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            assert_eq!(m.get("x"), Some(&BigUint::from(3u32)));
            assert_eq!(m.get("b"), Some(&BigUint::from(1u32)));
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}

/// Term-level ite SAT: the named FF variables must appear; the
/// skolem `__ite_N` is an implementation detail and is allowed to
/// be present or not.
#[test]
fn cdclt_sat_model_with_term_level_ite() {
    let src = r#"
(set-logic QF_FF)
(declare-fun c () Bool)
(declare-fun x () (_ FiniteField 101))
(assert (= (ite c x #f0m101) #f5m101))
"#;
    let q = parse_boolean(src).expect("parse");
    let r = solve_formula(q.prime.clone(), q.var_names(), &q.formula, &CancelToken::none());
    match r {
        SolveOutcome::Sat(m) => {
            let c_val = m.get("c").expect("c in model").clone();
            let x_val = m.get("x").expect("x in model").clone();
            // ite picks x when c is True (== 1).
            if c_val == BigUint::from(1u32) {
                assert_eq!(x_val, BigUint::from(5u32),
                    "c=1 ⇒ x must equal 5; got x={:?}", x_val);
            } else {
                panic!("c must be 1 for the equality to hold; got c={:?}", c_val);
            }
        }
        other => panic!("expected SAT, got {:?}", other),
    }
}
