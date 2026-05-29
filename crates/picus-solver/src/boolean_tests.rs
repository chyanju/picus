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
    // 4 ors × 2 = DNF length 16; cap 8 ⇒ Unknown. ConfigGuard
    // scopes the override so we don't need a cross-test lock.
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
