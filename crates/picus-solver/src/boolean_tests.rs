use super::*;

/// PolyTerm constructor: `coeff * <idx>^exp` (exp=0 → constant).
fn pt(coeff: u64, idx: u32, exp: u16) -> PolyTerm {
    let vars = if exp == 0 { vec![] } else { vec![(idx, exp)] };
    PolyTerm {
        coeff: BigUint::from(coeff),
        vars,
    }
}

/// Construct a builder pre-populated with the given var names.
fn builder_with_vars(prime: u64, names: &[&str]) -> ConstraintSystemBuilder {
    let mut b = ConstraintSystemBuilder::new(BigUint::from(prime));
    for n in names {
        b.var(n);
    }
    b
}

/// Build a Lit::Eq for `coeff * <var_idx> == rhs_const`.
fn lit_eq(coeff: u64, var_idx: u32, rhs_const: u64) -> Formula {
    Formula::Lit(Literal::Eq(
        vec![pt(coeff, var_idx, 1)],
        vec![pt(rhs_const, 0, 0)],
    ))
}

#[test]
fn nnf_distributes_not() {
    // Frame: x=0, y=1
    let f = Formula::Not(Box::new(Formula::And(vec![
        lit_eq(1, 0, 0),
        lit_eq(1, 1, 0),
    ])));
    let nnf = f.nnf();
    match nnf {
        Formula::Or(fs) => {
            assert_eq!(fs.len(), 2);
            for f in fs {
                matches!(f, Formula::Lit(Literal::Neq(_, _)));
            }
        }
        _ => panic!("expected Or after nnf"),
    }
}

#[test]
fn dnf_of_and_or() {
    // frame: a=0, b=1, c=2, d=3
    let a = lit_eq(1, 0, 0);
    let b = lit_eq(1, 1, 0);
    let c = lit_eq(1, 2, 0);
    let d = lit_eq(1, 3, 0);
    let f = Formula::And(vec![Formula::Or(vec![a, b]), Formula::Or(vec![c, d])]);
    let dnf = f.nnf().to_dnf();
    assert_eq!(dnf.len(), 4);
    for d in &dnf {
        assert_eq!(d.len(), 2);
    }
}

#[test]
fn dnf_false_propagates() {
    let f = Formula::And(vec![Formula::True, Formula::False]);
    let dnf = f.nnf().to_dnf();
    assert!(dnf.is_empty());
}

#[test]
fn dnf_true_is_single_empty_conj() {
    let dnf = Formula::True.nnf().to_dnf();
    assert_eq!(dnf.len(), 1);
    assert!(dnf[0].is_empty());
}

#[test]
fn disjunct_systems_split() {
    // or(x = 0, y = 0) → two ConstraintSystems
    let builder = builder_with_vars(101, &["x", "y"]);
    let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 0)]);
    let q = BooleanQuery::from_builder_and_formula(builder, f);
    let systems = q.to_disjunct_systems();
    assert_eq!(systems.len(), 2);
    assert_eq!(systems[0].equalities.len(), 1);
    assert_eq!(systems[1].equalities.len(), 1);
}

#[test]
fn solve_disjunctive_bit_sat() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    assert_eq!(q.dnf().len(), 1);
    let outcome = solve_boolean_query(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Sat(_)));
}

#[test]
fn disjunctive_bit_rewrites_pattern() {
    // Direct test of the rewrite pass: or(x=0, x=1) → x*x = x
    let prime = BigUint::from(101u32);
    let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 0, 1)]);
    let rewritten = rewrite_disjunctive_bit(f, &prime);
    match rewritten {
        Formula::Lit(Literal::Eq(lhs, rhs)) => {
            assert_eq!(lhs.len(), 1);
            assert_eq!(lhs[0].vars, vec![(0, 2)]);
            assert_eq!(rhs.len(), 1);
            assert_eq!(rhs[0].vars, vec![(0, 1)]);
        }
        _ => panic!("expected single Eq literal after disjunctive-bit rewrite"),
    }
}

fn outcome_kind(o: &SolveOutcome) -> &'static str {
    match o {
        SolveOutcome::Sat(_) => "sat",
        SolveOutcome::Unsat(_) => "unsat",
        SolveOutcome::Unknown => "unknown",
    }
}

fn assert_cdclt_dnf_agree(src: &str) {
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let cdclt_out = crate::cdclt::solve_formula(
        q.prime.clone(),
        q.var_names(),
        &q.formula,
        &CancelToken::none(),
    );
    let dnf_out = solve_boolean_query_dnf(&q, &CancelToken::none());
    assert_eq!(outcome_kind(&cdclt_out), outcome_kind(&dnf_out));
}

#[test]
fn cross_validate_disjunctive_bit() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F))))
";
    assert_cdclt_dnf_agree(src);
}

#[test]
fn cross_validate_unsat_chain() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff0 F)))
(assert (=> (= x (as ff0 F)) (= y (as ff0 F))))
(assert (not (= y (as ff0 F))))
";
    assert_cdclt_dnf_agree(src);
}

#[test]
fn cross_validate_or_with_distinct_branches() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
";
    assert_cdclt_dnf_agree(src);
}

#[test]
fn cross_validate_three_or_unsat() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff0 F)) (= x (as ff1 F)) (= x (as ff2 F))))
(assert (= x (as ff7 F)))
";
    assert_cdclt_dnf_agree(src);
}

#[test]
fn disjunctive_bit_does_not_match_unrelated_vars() {
    // or(x = 0, y = 1) — different vars, should NOT collapse.
    let prime = BigUint::from(101u32);
    let f = Formula::Or(vec![lit_eq(1, 0, 0), lit_eq(1, 1, 1)]);
    let rewritten = rewrite_disjunctive_bit(f, &prime);
    assert!(matches!(rewritten, Formula::Or(_)));
}

#[test]
fn solve_disjunctive_unsat() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (= x (as ff1 F)))
(assert (or (= x (as ff0 F)) (= x (as ff2 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_with_not_and_implies() {
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(declare-fun y () F)
(assert (= x (as ff0 F)))
(assert (=> (= x (as ff0 F)) (= y (as ff0 F))))
(assert (not (= y (as ff0 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Unsat(_)));
}

#[test]
fn dnf_size_estimate_lit_is_one() {
    let f = lit_eq(1, 0, 0);
    assert_eq!(f.dnf_size_estimate(1_000), 1);
}

#[test]
fn dnf_size_estimate_and_of_ors_multiplies() {
    // 5 fold and-of-ors with each or having 2 disjuncts → 2^5 = 32.
    // Use distinct indices 0..4 to keep literals over distinct vars.
    let ors: Vec<Formula> = (0..5)
        .map(|i| Formula::Or(vec![lit_eq(1, i as u32, 0), lit_eq(1, i as u32, 1)]))
        .collect();
    let f = Formula::And(ors).nnf();
    assert_eq!(f.dnf_size_estimate(1_000), 32);
    assert_eq!(f.to_dnf().len(), 32);
}

#[test]
fn dnf_size_estimate_saturates_at_cap() {
    let ors: Vec<Formula> = (0..30)
        .map(|i| Formula::Or(vec![lit_eq(1, i as u32, 0), lit_eq(1, i as u32, 1)]))
        .collect();
    let f = Formula::And(ors).nnf();
    let est = f.dnf_size_estimate(100_000);
    assert_eq!(est, 100_000);
}

#[test]
fn solve_boolean_query_dnf_returns_unknown_past_cap() {
    // 4 ors × 2 = DNF length 16; cap 8 ⇒ Unknown.
    let _g = crate::config::ConfigGuard::with_override(|c| {
        c.dnf_enabled = true;
        c.dnf_cap = 8;
    });
    let src = r#"
(define-sort F () (_ FiniteField 101))
(declare-fun a () F)
(declare-fun b () F)
(declare-fun c () F)
(declare-fun d () F)
(assert (or (= a (as ff5 F)) (= a (as ff6 F))))
(assert (or (= b (as ff5 F)) (= b (as ff6 F))))
(assert (or (= c (as ff5 F)) (= c (as ff6 F))))
(assert (or (= d (as ff5 F)) (= d (as ff6 F))))
"#;
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Unknown));
}

#[test]
fn nnf_not_neq_becomes_eq() {
    // ¬(a ≠ b) ⇒ (a = b): negation of a disequality is an equality with
    // the same terms.
    let f = Formula::Not(Box::new(Formula::Lit(Literal::Neq(
        vec![pt(1, 0, 1)],
        vec![pt(0, 0, 0)],
    ))));
    match f.nnf() {
        Formula::Lit(Literal::Eq(a, b)) => {
            assert_eq!(a.len(), 1);
            assert_eq!(a[0].coeff, BigUint::from(1u32));
            assert_eq!(a[0].vars, vec![(0u32, 1u16)]);
            assert_eq!(b.len(), 1);
            assert_eq!(b[0].coeff, BigUint::zero());
            assert!(b[0].vars.is_empty());
        }
        other => panic!("expected Eq literal after nnf, got {:?}", other),
    }
}

#[test]
fn nnf_not_true_is_false() {
    assert!(matches!(
        Formula::Not(Box::new(Formula::True)).nnf(),
        Formula::False
    ));
}

#[test]
fn nnf_not_false_is_true() {
    assert!(matches!(
        Formula::Not(Box::new(Formula::False)).nnf(),
        Formula::True
    ));
}

#[test]
fn dnf_true_direct_is_single_empty_conjunct() {
    let dnf = Formula::True.to_dnf();
    assert_eq!(dnf.len(), 1);
    assert!(dnf[0].is_empty());
}

#[test]
fn dnf_false_direct_is_empty() {
    let dnf = Formula::False.to_dnf();
    assert!(dnf.is_empty());
}

#[test]
fn dnf_of_and_with_false_disjunct_is_empty() {
    // And(lit, False) ⇒ the False conjunct collapses the whole DNF.
    let f = Formula::And(vec![lit_eq(1, 0, 0), Formula::False]);
    assert!(f.nnf().to_dnf().is_empty());
}

#[test]
fn dnf_size_estimate_or_saturates_at_cap() {
    // 30 single-literal OR disjuncts with cap 10 ⇒ the Or accumulator
    // saturates and returns cap.
    let disjuncts: Vec<Formula> = (0..30).map(|i| lit_eq(1, i as u32, 0)).collect();
    let f = Formula::Or(disjuncts);
    assert_eq!(f.dnf_size_estimate(10), 10);
}

#[test]
fn disjunct_systems_neq_preserves_zero_coefficient() {
    // Neq with a zero-coefficient `a` term: the negated coefficient stays
    // zero (no `prime - 0` wraparound) in the synthesized def equality.
    let builder = builder_with_vars(101, &["x", "y"]);
    let f = Formula::Lit(Literal::Neq(vec![pt(0, 0, 1)], vec![pt(1, 1, 1)]));
    let q = BooleanQuery::from_builder_and_formula(builder, f);
    let systems = q.to_disjunct_systems();
    assert_eq!(systems.len(), 1);
    let def = &systems[0].equalities[0];
    assert!(
        def.iter()
            .any(|t| t.coeff.is_zero() && t.vars == vec![(0u32, 1u16)]),
        "zero-coeff term for x must be preserved, not negated: {:?}",
        def
    );
}

#[test]
fn eq_normalized_poly_is_none_for_disequality() {
    let prime = BigUint::from(101u32);
    let lit = Literal::Neq(vec![pt(1, 0, 1)], vec![pt(0, 0, 0)]);
    assert!(eq_normalized_poly(&lit, &prime).is_none());
}

#[test]
fn parse_var_equals_const_rejects_multiple_var_terms() {
    // (x + y = 0): two distinct variable terms ⇒ no single-var match.
    let prime = BigUint::from(101u32);
    let lit = Literal::Eq(vec![pt(1, 0, 1), pt(1, 1, 1)], vec![pt(0, 0, 0)]);
    assert!(parse_var_equals_const(&lit, &prime).is_none());
}

#[test]
fn parse_var_equals_const_rejects_degree_two_term() {
    // (x^2 = 0): a degree-2 term ⇒ no single-var match.
    let prime = BigUint::from(101u32);
    let lit = Literal::Eq(vec![pt(1, 0, 2)], vec![pt(0, 0, 0)]);
    assert!(parse_var_equals_const(&lit, &prime).is_none());
}

#[test]
fn parse_var_equals_const_rejects_non_unit_coefficient() {
    // (2x = 0): coefficient is not 1 ⇒ no single-var-equals-const match.
    let prime = BigUint::from(101u32);
    let lit = Literal::Eq(vec![pt(2, 0, 1)], vec![pt(0, 0, 0)]);
    assert!(parse_var_equals_const(&lit, &prime).is_none());
}

#[test]
fn parse_var_equals_const_negates_nonzero_constant() {
    // (x = 5) over p=101 ⇒ (var 0, value 5). eq_normalized_poly forms
    // x - 5 (const coeff = 96 = -5), which parse re-negates to 5.
    let prime = BigUint::from(101u32);
    let lit = Literal::Eq(vec![pt(1, 0, 1)], vec![pt(5, 0, 0)]);
    let (idx, val) = parse_var_equals_const(&lit, &prime).expect("single-var match");
    assert_eq!(idx, 0);
    assert_eq!(val, BigUint::from(5u32));
}

#[test]
fn solve_boolean_query_dnf_empty_formula_is_unsat() {
    // A `False` formula expands to an empty DNF ⇒ no disjunct systems ⇒
    // vacuously UNSAT.
    let builder = builder_with_vars(101, &["x"]);
    let q = BooleanQuery::from_builder_and_formula(builder, Formula::False);
    assert!(q.dnf().is_empty());
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Unsat(_)));
}

#[test]
fn solve_boolean_query_dnf_all_disjuncts_unsat() {
    // (x = 1) ∧ (or (= x 0) (= x 2)): both DNF disjuncts contradict
    // x = 1 ⇒ every disjunct UNSAT ⇒ overall UNSAT with an empty core.
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (= x (as ff1 F)))
(assert (or (= x (as ff0 F)) (= x (as ff2 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
    match outcome {
        SolveOutcome::Unsat(core) => assert!(core.is_empty()),
        other => panic!("expected Unsat, got {:?}", outcome_kind(&other)),
    }
}

#[test]
fn solve_boolean_query_dnf_first_sat_disjunct_wins() {
    // (or (= x 5) (= x 6)): the first disjunct is satisfiable ⇒ SAT.
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Sat(_)));
}

#[test]
fn solve_boolean_query_routes_to_dnf_when_enabled() {
    // With dnf_enabled set, solve_boolean_query dispatches to the
    // DNF-enumeration path; a satisfiable query still returns SAT.
    let _g = crate::config::ConfigGuard::with_override(|c| {
        c.dnf_enabled = true;
        c.dnf_cap = 100_000;
    });
    let src = "\
(define-sort F () (_ FiniteField 101))
(declare-fun x () F)
(assert (or (= x (as ff5 F)) (= x (as ff6 F))))
";
    let q = crate::smt2::parse_boolean(src).expect("parse");
    let outcome = solve_boolean_query(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Sat(_)));
}

#[test]
#[should_panic(expected = "non-NNF input")]
fn to_dnf_panics_on_non_nnf_not_node() {
    // `to_dnf` documents that the caller must apply `nnf()` first; a raw
    // `Not` node hits the precondition panic rather than silently
    // producing a wrong DNF.
    let f = Formula::Not(Box::new(lit_eq(1, 0, 0)));
    let _ = f.to_dnf();
}

#[test]
#[should_panic(expected = "non-NNF input")]
fn dnf_size_estimate_panics_on_non_nnf_not_node() {
    // Same NNF precondition for the size estimate.
    let f = Formula::Not(Box::new(lit_eq(1, 0, 0)));
    let _ = f.dnf_size_estimate(1_000);
}

#[test]
fn dnf_size_estimate_true_is_one() {
    // A bare `True` estimates to a single (empty) disjunct.
    assert_eq!(Formula::True.dnf_size_estimate(1_000), 1);
}

#[test]
fn dnf_size_estimate_and_with_false_subterm_is_zero() {
    // And(True, False): the False conjunct estimates 0, short-circuiting
    // the product to 0 (matching to_dnf collapsing the whole And).
    let f = Formula::And(vec![Formula::True, Formula::False]);
    assert_eq!(f.dnf_size_estimate(1_000), 0);
    assert!(f.to_dnf().is_empty());
}

#[test]
fn solve_boolean_query_dnf_returns_unknown_when_cancelled_mid_enumeration() {
    // A pre-cancelled token with at least one disjunct system: the
    // per-disjunct cancel check fires before the first encode/solve and
    // returns Unknown.
    let _g = crate::config::ConfigGuard::with_override(|c| {
        c.dnf_enabled = true;
        c.dnf_cap = 100_000;
    });
    let builder = builder_with_vars(101, &["x"]);
    let f = Formula::Lit(Literal::Eq(vec![pt(1, 0, 1)], vec![pt(5, 0, 0)]));
    let q = BooleanQuery::from_builder_and_formula(builder, f);
    assert_eq!(q.dnf().len(), 1);
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::cancelled());
    assert!(matches!(outcome, SolveOutcome::Unknown));
}

#[test]
fn solve_boolean_query_dnf_encode_error_disjunct_yields_unknown() {
    // A disjunct whose equality references a variable index past the
    // builder frame fails to encode (`var_idx >= ring vars`). The
    // enumeration records the encode failure as Unknown and, with no SAT
    // disjunct, the overall result is Unknown.
    //
    // The builder has a single var (idx 0); the literal references idx 5.
    // With exactly one used var index its count equals var_names.len(), so
    // `compact_used_vars` short-circuits and the out-of-range index reaches
    // `encode`, which rejects it.
    let builder = builder_with_vars(101, &["a"]);
    let f = Formula::Lit(Literal::Eq(vec![pt(1, 5, 1)], vec![]));
    let q = BooleanQuery::from_builder_and_formula(builder, f);
    let systems = q.to_disjunct_systems();
    assert_eq!(systems.len(), 1);
    // The disjunct system carries the out-of-range index, so `encode`
    // returns Err — confirming the precondition the solver path relies on.
    assert!(encode(&systems[0]).is_err());
    let outcome = solve_boolean_query_dnf(&q, &CancelToken::none());
    assert!(matches!(outcome, SolveOutcome::Unknown));
}
