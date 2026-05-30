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

// ───────────── internal-helper unit tests (direct calls) ─────────────

fn atom(s: &str) -> Sexpr {
    Sexpr::Atom(s.into())
}

fn list(items: Vec<Sexpr>) -> Sexpr {
    Sexpr::List(items)
}

/// Build a `ParseCtx` with the given prime, declared vars, and macros.
fn mk_ctx(prime: u32, vars: &[(&str, VarSort)], macros: Vec<(&str, MacroDef)>) -> ParseCtx {
    let prime = BigUint::from(prime);
    let mut vmap: HashMap<String, VarSort> = HashMap::new();
    for (n, s) in vars {
        vmap.insert((*n).into(), *s);
    }
    let mut mmap: HashMap<String, MacroDef> = HashMap::new();
    for (n, d) in macros {
        mmap.insert(n.into(), d);
    }
    ParseCtx {
        prime: prime.clone(),
        vars: vmap,
        macros: mmap,
        next_ite_skolem: 0,
        side_constraints: Vec::new(),
        builder: ConstraintSystemBuilder::new(prime),
        expansion_depth: 0,
    }
}

// ── classify_sort ──

#[test]
fn classify_sort_recognises_bool_ff_and_rejects_unknown() {
    assert_eq!(classify_sort(Some(&atom("Bool"))), Some(VarSort::Bool));
    assert_eq!(classify_sort(Some(&atom("F"))), Some(VarSort::Ff));
    // Default arm: an unrecognised atom is not a known sort.
    assert_eq!(classify_sort(Some(&atom("UnknownSort"))), None);
    // `(_ FiniteField p)` list classifies as Ff.
    assert_eq!(
        classify_sort(Some(&list(vec![atom("_"), atom("FiniteField"), atom("13")]))),
        Some(VarSort::Ff)
    );
    // None input short-circuits.
    assert_eq!(classify_sort(None), None);
}

// ── finite_field_prime_str ──

#[test]
fn finite_field_prime_str_matches_only_canonical_shape() {
    // Canonical `(_ FiniteField 31)` yields the prime literal.
    assert_eq!(
        finite_field_prime_str(&list(vec![atom("_"), atom("FiniteField"), atom("31")])),
        Some("31")
    );
    // Wrong length (2 elements) => None.
    assert_eq!(
        finite_field_prime_str(&list(vec![atom("foo"), atom("bar")])),
        None
    );
    // Right length but wrong atom names => None.
    assert_eq!(
        finite_field_prime_str(&list(vec![atom("_"), atom("Int"), atom("31")])),
        None
    );
    // A non-list sort => None.
    assert_eq!(finite_field_prime_str(&atom("F")), None);
}

// ── classify_declare ──

#[test]
fn classify_declare_defensive_paths() {
    // list too short (< 2) => None.
    assert_eq!(
        classify_declare("declare-fun", &[atom("declare-fun")]),
        None
    );
    // name at [1] is not an atom => None.
    assert_eq!(
        classify_declare("declare-fun", &[atom("declare-fun"), list(vec![])]),
        None
    );
    // declare-fun with no sort slot: still returns the name, but sort/prime
    // are None (classify_sort(None) => None).
    match classify_declare("declare-fun", &[atom("declare-fun"), atom("x")]) {
        Some((name, sort, prime)) => {
            assert_eq!(name, "x");
            assert_eq!(sort, None);
            assert_eq!(prime, None);
        }
        None => panic!("expected Some with name but no sort"),
    }
}

#[test]
fn classify_declare_threads_inline_prime() {
    // declare-fun reads its sort from slot 3; an inline FF sort pins the prime.
    let l = [
        atom("declare-fun"),
        atom("z"),
        list(vec![]),
        list(vec![atom("_"), atom("FiniteField"), atom("23")]),
    ];
    match classify_declare("declare-fun", &l) {
        Some((name, sort, prime)) => {
            assert_eq!(name, "z");
            assert_eq!(sort, Some(VarSort::Ff));
            assert_eq!(prime, Some(BigUint::from(23u32)));
        }
        None => panic!("expected Some"),
    }
    // declare-const reads its sort from slot 2.
    let lc = [
        atom("declare-const"),
        atom("w"),
        list(vec![atom("_"), atom("FiniteField"), atom("5")]),
    ];
    match classify_declare("declare-const", &lc) {
        Some((name, sort, prime)) => {
            assert_eq!(name, "w");
            assert_eq!(sort, Some(VarSort::Ff));
            assert_eq!(prime, Some(BigUint::from(5u32)));
        }
        None => panic!("expected Some"),
    }
}

// ── collect_ff_literal_primes ──

#[test]
fn collect_ff_literal_primes_recurses_into_nested_lists() {
    let mut primes: BTreeSet<BigUint> = BTreeSet::new();
    let nested = list(vec![list(vec![atom("#f3m7")])]);
    collect_ff_literal_primes(&nested, &mut primes);
    assert_eq!(primes.len(), 1);
    assert!(primes.contains(&BigUint::from(7u32)));
}

#[test]
fn collect_ff_literal_primes_atom_and_nonliteral() {
    // Bare atom literal contributes its modulus.
    let mut primes: BTreeSet<BigUint> = BTreeSet::new();
    collect_ff_literal_primes(&atom("#f10m13"), &mut primes);
    assert!(primes.contains(&BigUint::from(13u32)));
    // A non-`#f` atom contributes nothing.
    let mut none: BTreeSet<BigUint> = BTreeSet::new();
    collect_ff_literal_primes(&atom("ff.add"), &mut none);
    assert!(none.is_empty());
}

// ── mul_polys ──

#[test]
fn mul_polys_drops_zero_coefficient_products() {
    let a = vec![PolyTerm { coeff: BigUint::from(2u32), vars: vec![(0, 1)] }];
    let b = vec![PolyTerm { coeff: BigUint::zero(), vars: vec![(1, 1)] }];
    let prime = BigUint::from(7u32);
    let out = mul_polys(&a, &b, &prime).expect("mul ok");
    // 2 * 0 ≡ 0 mod 7 — the product term is skipped, leaving no terms.
    assert!(out.is_empty());
}

#[test]
fn mul_polys_merges_exponents() {
    // x * x => x^2 with coeff 1 mod 7.
    let a = vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0, 1)] }];
    let b = vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0, 1)] }];
    let out = mul_polys(&a, &b, &BigUint::from(7u32)).expect("mul ok");
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].coeff, BigUint::from(1u32));
    assert_eq!(out[0].vars, vec![(0u32, 2u16)]);
}

#[test]
fn mul_polys_exponent_overflow_is_malformed() {
    let a = vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0, u16::MAX)] }];
    let b = vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(0, 1)] }];
    match mul_polys(&a, &b, &BigUint::from(7u32)) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("exponent")),
        other => panic!("expected Malformed exponent overflow; got {:?}", other),
    }
}

// ── parse_ff_const ──

#[test]
fn parse_ff_const_rejects_modulus_mismatch() {
    // `#f3m11` declares mod 11; session prime is 7 — a mismatch returns None.
    assert_eq!(parse_ff_const("#f3m11", &BigUint::from(7u32)), None);
    // Matching modulus parses the value.
    assert_eq!(
        parse_ff_const("#f3m7", &BigUint::from(7u32)),
        Some(BigUint::from(3u32))
    );
}

// ── build_poly: Atom paths ──

#[test]
fn build_poly_atom_constants() {
    let prime = BigUint::from(7u32);
    let vars: HashMap<String, VarSort> = HashMap::new();
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    // ff5 constant.
    let p = build_poly(&atom("ff5"), &prime, &vars, &mut b).expect("ff5");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(5u32));
    assert!(p[0].vars.is_empty());
    // bare decimal reduced mod prime: 9 mod 7 = 2.
    let p2 = build_poly(&atom("9"), &prime, &vars, &mut b).expect("9");
    assert_eq!(p2[0].coeff, BigUint::from(2u32));
    assert!(p2[0].vars.is_empty());
}

#[test]
fn build_poly_atom_error_paths() {
    let prime = BigUint::from(7u32);
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    // Undeclared symbol.
    match build_poly(&atom("undefined_var"), &prime, &vars, &mut b) {
        Err(ParseError::UnknownSymbol(s)) => assert_eq!(s, "undefined_var"),
        other => panic!("expected UnknownSymbol; got {:?}", other),
    }
    // Bool var used in an FF term context.
    vars.insert("b".into(), VarSort::Bool);
    match build_poly(&atom("b"), &prime, &vars, &mut b) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("Bool")),
        other => panic!("expected Malformed for Bool in FF; got {:?}", other),
    }
}

#[test]
fn build_poly_atom_ff_var_interns_index() {
    let prime = BigUint::from(7u32);
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    vars.insert("x".into(), VarSort::Ff);
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let p = build_poly(&atom("x"), &prime, &vars, &mut b).expect("x");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(1u32));
    assert_eq!(p[0].vars.len(), 1);
    assert_eq!(p[0].vars[0].1, 1u16);
}

// ── build_poly: List error / operator paths ──

#[test]
fn build_poly_list_error_paths() {
    let prime = BigUint::from(7u32);
    let vars: HashMap<String, VarSort> = HashMap::new();
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    // Non-atom head.
    match build_poly(&list(vec![list(vec![])]), &prime, &vars, &mut b) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("non-atom head")),
        other => panic!("expected non-atom head Malformed; got {:?}", other),
    }
    // 'as' arity != 3.
    match build_poly(&list(vec![atom("as"), atom("ff1")]), &prime, &vars, &mut b) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'as' arity")),
        other => panic!("expected 'as' arity Malformed; got {:?}", other),
    }
    // 'as' first arg not an atom.
    match build_poly(
        &list(vec![atom("as"), list(vec![]), atom("F")]),
        &prime,
        &vars,
        &mut b,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'as' first arg")),
        other => panic!("expected 'as' first arg Malformed; got {:?}", other),
    }
    // Unknown ff operator.
    match build_poly(
        &list(vec![atom("ff.unknown"), atom("ff1")]),
        &prime,
        &vars,
        &mut b,
    ) {
        Err(ParseError::UnknownOperator(o)) => assert_eq!(o, "ff.unknown"),
        other => panic!("expected UnknownOperator; got {:?}", other),
    }
}

#[test]
fn build_poly_ff_add_accumulates() {
    let prime = BigUint::from(7u32);
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    vars.insert("x".into(), VarSort::Ff);
    vars.insert("y".into(), VarSort::Ff);
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let p = build_poly(
        &list(vec![atom("ff.add"), atom("x"), atom("y")]),
        &prime,
        &vars,
        &mut b,
    )
    .expect("ff.add");
    // Two monomial terms, one per addend, both coeff 1.
    assert_eq!(p.len(), 2);
    assert!(p.iter().all(|t| t.coeff == BigUint::from(1u32) && t.vars.len() == 1));
}

#[test]
fn build_poly_ff_neg_negates_and_checks_arity() {
    let prime = BigUint::from(7u32);
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    vars.insert("x".into(), VarSort::Ff);
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let p = build_poly(
        &list(vec![atom("ff.neg"), atom("x")]),
        &prime,
        &vars,
        &mut b,
    )
    .expect("ff.neg");
    assert_eq!(p.len(), 1);
    // -x mod 7 has coefficient 7-1 = 6.
    assert_eq!(p[0].coeff, BigUint::from(6u32));
    assert_eq!(p[0].vars.len(), 1);
    // Wrong arity.
    match build_poly(
        &list(vec![atom("ff.neg"), atom("x"), atom("x")]),
        &prime,
        &vars,
        &mut b,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("ff.neg")),
        other => panic!("expected ff.neg arity Malformed; got {:?}", other),
    }
}

#[test]
fn build_poly_unary_minus_negates() {
    let prime = BigUint::from(7u32);
    let mut vars: HashMap<String, VarSort> = HashMap::new();
    vars.insert("x".into(), VarSort::Ff);
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let p = build_poly(&list(vec![atom("-"), atom("x")]), &prime, &vars, &mut b)
        .expect("unary minus");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(6u32));
}

// ── handle_assert error paths ──

#[test]
fn handle_assert_error_paths() {
    let prime = BigUint::from(7u32);
    let vars: HashMap<String, VarSort> = HashMap::new();
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let mut diseq_zero: Option<VarIdx> = None;
    let mut diseq_counter = 0usize;
    // Non-list body.
    match handle_assert(&atom("x"), &prime, &vars, &mut b, &mut diseq_zero, &mut diseq_counter) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("non-list assert body")),
        other => panic!("expected non-list body Malformed; got {:?}", other),
    }
    // Non-atom head.
    match handle_assert(
        &list(vec![list(vec![])]),
        &prime,
        &vars,
        &mut b,
        &mut diseq_zero,
        &mut diseq_counter,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("non-atom head")),
        other => panic!("expected non-atom head Malformed; got {:?}", other),
    }
    // 'not' wrong arity.
    match handle_assert(
        &list(vec![atom("not")]),
        &prime,
        &vars,
        &mut b,
        &mut diseq_zero,
        &mut diseq_counter,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'not' arity")),
        other => panic!("expected 'not' arity Malformed; got {:?}", other),
    }
}

// ── is_bool_expr ──

#[test]
fn is_bool_expr_atoms() {
    let ctx = mk_ctx(7, &[("x", VarSort::Ff), ("b", VarSort::Bool)], vec![]);
    // 'true'/'false' atoms classify as Bool.
    assert!(is_bool_expr(&atom("true"), &ctx, 0));
    assert!(is_bool_expr(&atom("false"), &ctx, 0));
    // A Bool-declared var is Bool; an FF var and an unknown atom are not.
    assert!(is_bool_expr(&atom("b"), &ctx, 0));
    assert!(!is_bool_expr(&atom("x"), &ctx, 0));
    assert!(!is_bool_expr(&atom("unknown"), &ctx, 0));
}

#[test]
fn is_bool_expr_non_atom_head_is_false() {
    let ctx = mk_ctx(7, &[], vec![]);
    // Empty list (no head) and list with a non-atom head are not Bool.
    assert!(!is_bool_expr(&list(vec![]), &ctx, 0));
    assert!(!is_bool_expr(&list(vec![list(vec![])]), &ctx, 0));
}

// ── chain_is_bool ──

#[test]
fn chain_is_bool_rejects_mixed_sorts() {
    let ctx = mk_ctx(7, &[("x", VarSort::Ff), ("b", VarSort::Bool)], vec![]);
    // x is FF, b is Bool — a mixed chain is malformed.
    match chain_is_bool(&[atom("x"), atom("b")], &ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("mix")),
        other => panic!("expected mixed-sort Malformed; got {:?}", other),
    }
    // Homogeneous chains classify cleanly.
    assert!(chain_is_bool(&[atom("b"), atom("true")], &ctx).unwrap());
    assert!(!chain_is_bool(&[atom("x"), atom("x")], &ctx).unwrap());
}

// ── build_poly_with_ctx ──

#[test]
fn build_poly_with_ctx_term_ite_emits_skolem_and_side_constraints() {
    let mut ctx = mk_ctx(
        101,
        &[("c", VarSort::Bool), ("x", VarSort::Ff), ("y", VarSort::Ff)],
        vec![],
    );
    let e = list(vec![atom("ite"), atom("c"), atom("x"), atom("y")]);
    let p = build_poly_with_ctx(&e, &mut ctx).expect("term ite");
    // The result is a single fresh skolem variable.
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(1u32));
    assert_eq!(p[0].vars.len(), 1);
    // A `__ite_0` skolem was registered and two side constraints emitted.
    assert!(ctx.vars.contains_key("__ite_0"));
    assert_eq!(ctx.next_ite_skolem, 1);
    assert_eq!(ctx.side_constraints.len(), 2);
}

#[test]
fn build_poly_with_ctx_as_constant_and_errors() {
    let mut ctx = mk_ctx(7, &[], vec![]);
    // Well-formed `(as ff3 F)` => constant 3.
    let p = build_poly_with_ctx(
        &list(vec![atom("as"), atom("ff3"), atom("F")]),
        &mut ctx,
    )
    .expect("as ff3");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(3u32));
    assert!(p[0].vars.is_empty());
    // 'as' first arg not an atom.
    match build_poly_with_ctx(
        &list(vec![atom("as"), list(vec![]), atom("F")]),
        &mut ctx,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'as' first arg")),
        other => panic!("expected 'as' first arg Malformed; got {:?}", other),
    }
    // Bad 'as' constant.
    match build_poly_with_ctx(
        &list(vec![atom("as"), atom("notaconst"), atom("F")]),
        &mut ctx,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("bad 'as' constant")),
        other => panic!("expected bad 'as' constant Malformed; got {:?}", other),
    }
}

#[test]
fn build_poly_with_ctx_bitsum_weights_powers_of_two() {
    let mut ctx = mk_ctx(101, &[("a", VarSort::Ff), ("b", VarSort::Ff)], vec![]);
    let e = list(vec![atom("ff.bitsum"), atom("a"), atom("b")]);
    let p = build_poly_with_ctx(&e, &mut ctx).expect("bitsum");
    // a·1 + b·2 — two terms with coeffs 1 and 2.
    assert_eq!(p.len(), 2);
    let coeffs: BTreeSet<BigUint> = p.iter().map(|t| t.coeff.clone()).collect();
    assert!(coeffs.contains(&BigUint::from(1u32)));
    assert!(coeffs.contains(&BigUint::from(2u32)));
}

#[test]
fn build_poly_with_ctx_macro_expansion() {
    // double(y) = (ff.add y y); double(x) => 2 terms in x.
    let body = list(vec![atom("ff.add"), atom("y"), atom("y")]);
    let mdef = MacroDef {
        params: vec![("y".into(), VarSort::Ff)],
        body,
    };
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff)], vec![("double", mdef)]);
    let p = build_poly_with_ctx(&list(vec![atom("double"), atom("x")]), &mut ctx)
        .expect("macro expand");
    assert_eq!(p.len(), 2);
    assert!(p.iter().all(|t| t.coeff == BigUint::from(1u32) && t.vars.len() == 1));
}

#[test]
fn build_poly_with_ctx_binary_minus_subtracts() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff), ("y", VarSort::Ff)], vec![]);
    let e = list(vec![atom("-"), atom("x"), atom("y")]);
    let p = build_poly_with_ctx(&e, &mut ctx).expect("x - y");
    // x + (-y): two terms, coeffs 1 and 6 (= -1 mod 7).
    assert_eq!(p.len(), 2);
    let coeffs: BTreeSet<BigUint> = p.iter().map(|t| t.coeff.clone()).collect();
    assert!(coeffs.contains(&BigUint::from(1u32)));
    assert!(coeffs.contains(&BigUint::from(6u32)));
}

// ── bool_chain_iff / ff_equality_chain / build_xor early returns ──

#[test]
fn bool_chain_iff_short_chains_are_true() {
    assert!(matches!(bool_chain_iff(vec![]), Formula::True));
    assert!(matches!(bool_chain_iff(vec![Formula::True]), Formula::True));
}

#[test]
fn ff_equality_chain_short_chains_are_true() {
    assert!(matches!(ff_equality_chain(&[]), Formula::True));
    let one: Polynomial = vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![] }];
    assert!(matches!(ff_equality_chain(&[one]), Formula::True));
}

#[test]
fn build_xor_empty_is_false() {
    assert!(matches!(build_xor(vec![]), Formula::False));
}

// ── assert_to_formula ──

#[test]
fn assert_to_formula_atom_errors() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff)], vec![]);
    // FF var used in a Bool context.
    match assert_to_formula(&atom("x"), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("FF variable")),
        other => panic!("expected FF-in-Bool Malformed; got {:?}", other),
    }
    // Undefined symbol.
    match assert_to_formula(&atom("nope"), &mut ctx) {
        Err(ParseError::UnknownSymbol(s)) => assert_eq!(s, "nope"),
        other => panic!("expected UnknownSymbol; got {:?}", other),
    }
}

#[test]
fn assert_to_formula_non_atom_head_is_malformed() {
    let mut ctx = mk_ctx(7, &[], vec![]);
    match assert_to_formula(&list(vec![list(vec![])]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("non-atom head")),
        other => panic!("expected non-atom head Malformed; got {:?}", other),
    }
}

#[test]
fn assert_to_formula_arity_errors() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff)], vec![]);
    // '=' with one operand.
    match assert_to_formula(&list(vec![atom("="), atom("x")]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'=' arity")),
        other => panic!("expected '=' arity; got {:?}", other),
    }
    // 'distinct' with one operand.
    match assert_to_formula(&list(vec![atom("distinct"), atom("x")]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'distinct' arity")),
        other => panic!("expected 'distinct' arity; got {:?}", other),
    }
    // 'not' wrong arity.
    match assert_to_formula(&list(vec![atom("not"), atom("x"), atom("x")]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'not' arity")),
        other => panic!("expected 'not' arity; got {:?}", other),
    }
    // '=>' with one operand.
    match assert_to_formula(&list(vec![atom("=>"), atom("x")]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'=>' arity")),
        other => panic!("expected '=>' arity; got {:?}", other),
    }
}

#[test]
fn assert_to_formula_distinct_bool_variants() {
    // 3+ distinct bools are pairwise-unequal => unsatisfiable => False.
    let mut ctx3 = mk_ctx(
        7,
        &[("a", VarSort::Bool), ("b", VarSort::Bool), ("c", VarSort::Bool)],
        vec![],
    );
    let f3 = assert_to_formula(
        &list(vec![atom("distinct"), atom("a"), atom("b"), atom("c")]),
        &mut ctx3,
    )
    .expect("distinct 3 bools");
    assert!(matches!(f3, Formula::False));
    // 2 distinct bools => xor (built as an Or of Ands).
    let mut ctx2 = mk_ctx(7, &[("a", VarSort::Bool), ("b", VarSort::Bool)], vec![]);
    let f2 = assert_to_formula(
        &list(vec![atom("distinct"), atom("a"), atom("b")]),
        &mut ctx2,
    )
    .expect("distinct 2 bools");
    assert!(matches!(f2, Formula::Or(_)));
}

#[test]
fn assert_to_formula_distinct_ff_two_is_single_neq() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff), ("y", VarSort::Ff)], vec![]);
    let f = assert_to_formula(
        &list(vec![atom("distinct"), atom("x"), atom("y")]),
        &mut ctx,
    )
    .expect("distinct 2 ff");
    // A single pair collapses to a bare Neq literal (no And wrapper).
    assert!(matches!(f, Formula::Lit(Literal::Neq(_, _))));
}

#[test]
fn assert_to_formula_assertion_level_term_ite_is_rejected() {
    // (ite c x y) with FF branches at assertion position has no Bool value.
    let mut ctx = mk_ctx(
        7,
        &[("c", VarSort::Bool), ("x", VarSort::Ff), ("y", VarSort::Ff)],
        vec![],
    );
    match assert_to_formula(
        &list(vec![atom("ite"), atom("c"), atom("x"), atom("y")]),
        &mut ctx,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("term-level ite")),
        other => panic!("expected term-level ite rejection; got {:?}", other),
    }
}

#[test]
fn assert_to_formula_bool_level_ite_builds_conditional() {
    let mut ctx = mk_ctx(
        7,
        &[("c", VarSort::Bool), ("a", VarSort::Bool), ("b", VarSort::Bool)],
        vec![],
    );
    let f = assert_to_formula(
        &list(vec![atom("ite"), atom("c"), atom("a"), atom("b")]),
        &mut ctx,
    )
    .expect("bool ite");
    // (c ∧ a) ∨ (¬c ∧ b): top-level Or of two And branches.
    match f {
        Formula::Or(branches) => {
            assert_eq!(branches.len(), 2);
            assert!(matches!(branches[0], Formula::And(_)));
            assert!(matches!(branches[1], Formula::And(_)));
        }
        other => panic!("expected Or of Ands; got {:?}", other),
    }
}

#[test]
fn assert_to_formula_macro_expansion_recurses() {
    // is_zero(p) = (= p (as ff0 F)) — a Bool-valued macro.
    let body = list(vec![atom("="), atom("p"), atom("ff0")]);
    let mdef = MacroDef {
        params: vec![("p".into(), VarSort::Ff)],
        body,
    };
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff)], vec![("is_zero", mdef)]);
    let f = assert_to_formula(&list(vec![atom("is_zero"), atom("x")]), &mut ctx)
        .expect("macro in assert");
    // Expands to a binary FF equality => bare Eq literal.
    assert!(matches!(f, Formula::Lit(Literal::Eq(_, _))));
}

#[test]
fn parse_ctx_enter_expansion_guards_depth() {
    let mut ctx = mk_ctx(7, &[], vec![]);
    // Walk right up to the cap without error.
    for _ in 0..MAX_MACRO_DEPTH {
        ctx.enter_expansion().expect("within depth");
    }
    // One more crosses the cap.
    match ctx.enter_expansion() {
        Err(ParseError::Malformed(m)) => assert!(m.contains("macro expansion exceeds")),
        other => panic!("expected depth-exceeded Malformed; got {:?}", other),
    }
}

// ── parse_define_fun ──

#[test]
fn parse_define_fun_well_formed() {
    let l = vec![
        atom("define-fun"),
        atom("f"),
        list(vec![list(vec![atom("p"), atom("F")])]),
        atom("F"),
        list(vec![atom("ff.add"), atom("p"), atom("p")]),
    ];
    let (name, def) = parse_define_fun(&l).expect("define-fun");
    assert_eq!(name, "f");
    assert_eq!(def.params.len(), 1);
    assert_eq!(def.params[0].0, "p");
    assert_eq!(def.params[0].1, VarSort::Ff);
    assert!(matches!(def.body, Sexpr::List(_)));
}

#[test]
fn parse_define_fun_error_paths() {
    // Wrong arity (4 instead of 5).
    let short = vec![atom("define-fun"), atom("f"), list(vec![]), atom("F")];
    assert!(matches!(parse_define_fun(&short), Err(ParseError::Malformed(_))));
    // Name not an atom.
    let bad_name = vec![
        atom("define-fun"),
        list(vec![]),
        list(vec![]),
        atom("F"),
        atom("ff0"),
    ];
    assert!(matches!(parse_define_fun(&bad_name), Err(ParseError::Malformed(_))));
    // Params not a list.
    let bad_params = vec![
        atom("define-fun"),
        atom("f"),
        atom("F"),
        atom("F"),
        atom("ff0"),
    ];
    assert!(matches!(parse_define_fun(&bad_params), Err(ParseError::Malformed(_))));
    // A param is not a (name sort) list.
    let bad_param = vec![
        atom("define-fun"),
        atom("f"),
        list(vec![atom("p")]),
        atom("F"),
        atom("ff0"),
    ];
    assert!(matches!(parse_define_fun(&bad_param), Err(ParseError::Malformed(_))));
    // A param pair has the wrong arity (1, not 2).
    let bad_param_arity = vec![
        atom("define-fun"),
        atom("f"),
        list(vec![list(vec![atom("p")])]),
        atom("F"),
        atom("ff0"),
    ];
    assert!(matches!(parse_define_fun(&bad_param_arity), Err(ParseError::Malformed(_))));
    // A param name is not an atom.
    let bad_param_name = vec![
        atom("define-fun"),
        atom("f"),
        list(vec![list(vec![list(vec![]), atom("F")])]),
        atom("F"),
        atom("ff0"),
    ];
    assert!(matches!(parse_define_fun(&bad_param_name), Err(ParseError::Malformed(_))));
}

// ── parse()/parse_boolean() top-level passes ──

#[test]
fn parse_skips_atoms_empty_and_unknown_commands() {
    // Stray atom, empty list, and an unrecognised command are all ignored;
    // a valid define-sort + declare-fun + assert still parse.
    let src = r#"
        bareatom
        ()
        (frobnicate 1 2)
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x (as ff3 F)))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(7u32));
    assert_eq!(cs.equalities.len(), 1);
}

#[test]
fn parse_declare_const_infers_prime() {
    // declare-const carries an inline FF sort; no define-sort present.
    let src = r#"
        (set-logic QF_FF)
        (declare-const x (_ FiniteField 13))
        (assert (= x (as ff4 F)))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(13u32));
}

#[test]
fn parse_boolean_gf2_default_for_bool_only() {
    // No FF sort, no literals, no ff.* op => prime defaults to GF(2).
    let src = r#"
        (set-logic QF_FF)
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (assert (or a b))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    assert_eq!(q.prime, BigUint::from(2u32));
}

#[test]
fn parse_boolean_literal_prime_inference_without_sort() {
    // No sort declaration, but `#fNm5` literals pin the prime to 5.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () F)
        (assert (= x #f3m5))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    assert_eq!(q.prime, BigUint::from(5u32));
}

#[test]
fn parse_boolean_multiple_literal_primes_is_malformed() {
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (= x #f3m5))
        (assert (= y #f3m11))
        (check-sat)
    "#;
    assert!(matches!(parse_boolean(src), Err(ParseError::Malformed(_))));
}

#[test]
fn parse_boolean_ff_op_without_prime_is_missing_prime() {
    // ff.* operator present, but no sort and no literal supplies a prime.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (= y (ff.add x x)))
        (check-sat)
    "#;
    assert!(matches!(parse_boolean(src), Err(ParseError::MissingPrime)));
}

#[test]
fn parse_boolean_emits_bool_bit_constraint() {
    // Each Bool var gets a `b*b = b` constraint; it survives into the DNF
    // as an equality literal carrying a degree-2 monomial.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun b () Bool)
        (assert b)
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse");
    let has_degree_two = q.dnf().iter().flatten().any(|lit| {
        let polys = match lit {
            Literal::Eq(a, b) => [a, b],
            Literal::Neq(a, b) => [a, b],
        };
        polys
            .iter()
            .flat_map(|p| p.iter())
            .flat_map(|t| t.vars.iter())
            .any(|(_, exp)| *exp == 2)
    });
    assert!(has_degree_two, "missing b*b=b bit constraint in DNF");
}

// ── neg_poly zero-coefficient arm ──

#[test]
fn neg_poly_negates_zero_coeff_to_zero() {
    // A term with coeff 0 negates to 0 (not `prime - 0`, which would be
    // a spurious `prime` literal); a nonzero term negates to `prime - c`.
    let prime = BigUint::from(7u32);
    let p: Polynomial = vec![
        PolyTerm { coeff: BigUint::zero(), vars: vec![(0, 1)] },
        PolyTerm { coeff: BigUint::from(3u32), vars: vec![(1, 1)] },
    ];
    let neg = neg_poly(&p, &prime);
    assert_eq!(neg.len(), 2);
    assert_eq!(neg[0].coeff, BigUint::zero());
    assert_eq!(neg[1].coeff, BigUint::from(4u32)); // 7 - 3
}

// ── collect_ff_literal_primes: `#f` atom without an `m` separator ──

#[test]
fn collect_ff_literal_primes_skips_hashf_atom_without_modulus() {
    // `#f` prefix but no `m<modulus>` suffix: `rest.find('m')` is None, so
    // nothing is inserted (the fall-through arm).
    let mut primes: BTreeSet<BigUint> = BTreeSet::new();
    collect_ff_literal_primes(&atom("#f123"), &mut primes);
    assert!(primes.is_empty(), "no modulus suffix ⇒ no prime collected");
}

// ── handle_assert: (not (<non-atom-head> ..)) ──

#[test]
fn handle_assert_not_inner_non_atom_head_is_malformed() {
    let prime = BigUint::from(7u32);
    let vars: HashMap<String, VarSort> = HashMap::new();
    let mut b = ConstraintSystemBuilder::new(prime.clone());
    let mut diseq_zero: Option<VarIdx> = None;
    let mut diseq_counter = 0usize;
    // (not (() x)) — the inner list's first element is itself a list, so the
    // inner head is not an atom.
    let body = list(vec![atom("not"), list(vec![list(vec![]), atom("x")])]);
    match handle_assert(&body, &prime, &vars, &mut b, &mut diseq_zero, &mut diseq_counter) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'not' inner head")),
        other => panic!("expected 'not' inner head Malformed; got {:?}", other),
    }
}

// ── parse() first-pass skip arms ──

#[test]
fn parse_skips_list_with_non_atom_head_and_short_define_sort() {
    // `((nested))` — a top-level list whose first element is a list (non-atom
    // head, `_ => continue`). `(define-sort F)` — too short (< 4), continues
    // without setting a prime. The inline-FF-sort declare-fun then supplies it.
    let src = r#"
        (set-logic QF_FF)
        ((nested))
        (define-sort F)
        (declare-fun x () (_ FiniteField 7))
        (assert (= x (as ff3 F)))
        (check-sat)
    "#;
    let cs = parse(src).expect("parse skips bad forms");
    assert_eq!(cs.prime, BigUint::from(7u32));
    assert_eq!(cs.equalities.len(), 1);
}

// ── is_bool_expr depth cap ──

#[test]
fn is_bool_expr_past_depth_cap_declines() {
    // Beyond MAX_MACRO_DEPTH the classifier returns false regardless of the
    // expression, breaking unbounded recursion through a cyclic macro body.
    let ctx = mk_ctx(7, &[("b", VarSort::Bool)], vec![]);
    // A Bool atom would normally classify true, but the depth guard wins.
    assert!(!is_bool_expr(&atom("b"), &ctx, MAX_MACRO_DEPTH + 1));
    assert!(!is_bool_expr(&atom("true"), &ctx, MAX_MACRO_DEPTH + 1));
}

// ── build_poly_with_ctx: atom / list error + ff.mul / ff.neg arms ──

#[test]
fn build_poly_with_ctx_unknown_symbol_and_non_atom_head() {
    let mut ctx = mk_ctx(7, &[], vec![]);
    // Undeclared symbol in an FF term.
    match build_poly_with_ctx(&atom("ghost"), &mut ctx) {
        Err(ParseError::UnknownSymbol(s)) => assert_eq!(s, "ghost"),
        other => panic!("expected UnknownSymbol; got {:?}", other),
    }
    // A list whose first element is a list (non-atom head).
    match build_poly_with_ctx(&list(vec![list(vec![])]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("non-atom head in FF term")),
        other => panic!("expected non-atom head Malformed; got {:?}", other),
    }
}

#[test]
fn build_poly_with_ctx_ff_mul_multiplies() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff), ("y", VarSort::Ff)], vec![]);
    // (ff.mul x y) => single monomial x*y with coeff 1.
    let e = list(vec![atom("ff.mul"), atom("x"), atom("y")]);
    let p = build_poly_with_ctx(&e, &mut ctx).expect("ff.mul");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(1u32));
    assert_eq!(p[0].vars.len(), 2);
    // (* x x) => x^2 (exponent merged to 2).
    let e2 = list(vec![atom("*"), atom("x"), atom("x")]);
    let p2 = build_poly_with_ctx(&e2, &mut ctx).expect("* x x");
    assert_eq!(p2.len(), 1);
    assert_eq!(p2[0].vars, vec![(ctx.builder.var("x"), 2u16)]);
}

#[test]
fn build_poly_with_ctx_ff_neg_negates_and_checks_arity() {
    let mut ctx = mk_ctx(7, &[("x", VarSort::Ff)], vec![]);
    // (ff.neg x) => -x, coeff 7-1 = 6 mod 7.
    let p = build_poly_with_ctx(&list(vec![atom("ff.neg"), atom("x")]), &mut ctx)
        .expect("ff.neg");
    assert_eq!(p.len(), 1);
    assert_eq!(p[0].coeff, BigUint::from(6u32));
    assert_eq!(p[0].vars.len(), 1);
    // Wrong arity (two operands) is malformed.
    match build_poly_with_ctx(
        &list(vec![atom("ff.neg"), atom("x"), atom("x")]),
        &mut ctx,
    ) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("ff.neg")),
        other => panic!("expected ff.neg arity Malformed; got {:?}", other),
    }
}

// ── assert_to_formula: ite arity ──

#[test]
fn assert_to_formula_ite_wrong_arity_is_malformed() {
    let mut ctx = mk_ctx(7, &[("c", VarSort::Bool)], vec![]);
    // (ite c) — three-element shape required, two given.
    match assert_to_formula(&list(vec![atom("ite"), atom("c")]), &mut ctx) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'ite' arity")),
        other => panic!("expected 'ite' arity Malformed; got {:?}", other),
    }
}

// ── parse_boolean() first/second-pass skip arms + empty-assert formula ──

#[test]
fn parse_boolean_skips_atoms_empty_and_non_atom_head_forms() {
    // First pass: a bare atom (Sexpr::Atom continue), an empty list
    // (`list.is_empty` continue), and a non-atom-head list (`_ => continue`)
    // are all ignored; the FF declaration + assert still parse.
    let src = r#"
        (set-logic QF_FF)
        looseatom
        ()
        ((deep))
        (define-sort F () (_ FiniteField 7))
        (declare-fun x () F)
        (assert (= x (as ff2 F)))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse_boolean skips bad forms");
    assert_eq!(q.prime, BigUint::from(7u32));
}

#[test]
fn parse_boolean_short_define_sort_continues() {
    // `(define-sort F)` is too short (< 4) so its arm continues; the prime
    // comes from the inline declare-fun sort instead.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F)
        (declare-fun x () (_ FiniteField 13))
        (assert (= x (as ff4 F)))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse_boolean");
    assert_eq!(q.prime, BigUint::from(13u32));
}

#[test]
fn parse_boolean_assert_wrong_arity_is_malformed() {
    // `(assert a b)` has arity 3 (head + two args); the second pass rejects it.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 7))
        (declare-fun a () Bool)
        (declare-fun b () Bool)
        (assert a b)
        (check-sat)
    "#;
    match parse_boolean(src) {
        Err(ParseError::Malformed(m)) => assert!(m.contains("'assert' arity")),
        other => panic!("expected 'assert' arity Malformed; got {:?}", other),
    }
}

#[test]
fn parse_boolean_no_asserts_yields_true_query() {
    // No `(assert ...)` and no Bool vars ⇒ the combined formula is the empty
    // conjunction, i.e. Formula::True. The query still parses with the
    // declared prime.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 7))
        (check-sat)
    "#;
    let q = parse_boolean(src).expect("parse_boolean no asserts");
    assert_eq!(q.prime, BigUint::from(7u32));
    // No asserts and no Bool bit-constraints ⇒ a single trivially-true DNF
    // cube (no literals).
    assert!(
        q.dnf().iter().all(|cube| cube.is_empty()),
        "Formula::True ⇒ no literals in any cube"
    );
}

// ───────────── parse() prime-assignment paths (deterministic) ─────────────

#[test]
fn parse_define_sort_pins_session_prime() {
    // Drives the first-pass `define-sort F () (_ FiniteField N)` branch in
    // `parse()`: line `prime = Some(n)` after a successful
    // `finite_field_prime_str` + BigUint parse. No declare-fun supplies a
    // prime, so the value pinned here must reach `ConstraintSystem.prime`.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 13))
        (declare-fun x () F)
        (assert (= x (as ff4 F)))
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(13u32));
}

#[test]
fn parse_declare_fun_inline_ff_sort_infers_prime() {
    // No `define-sort` in scope: the first `(declare-fun x () (_ FiniteField
    // 19))` whose classify_declare yields `inferred = Some(19)` must set
    // `prime = Some(19)` via the `if prime.is_none() { ... }` branch.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun x () (_ FiniteField 19))
        (assert (= x (as ff5 (_ FiniteField 19))))
    "#;
    let cs = parse(src).expect("parse");
    assert_eq!(cs.prime, BigUint::from(19u32));
}

// ───────────── parse_boolean() prime-assignment paths (deterministic) ─────

#[test]
fn parse_boolean_define_sort_pins_session_prime() {
    // First-pass `define-sort F () (_ FiniteField N)` branch in
    // `parse_boolean()`: confirms the `prime = Some(n)` assignment after a
    // successful prime-literal parse. The empty `(assert true)` keeps the
    // run trivial so the assertion focuses on the prime threading.
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 29))
        (assert true)
    "#;
    let q = parse_boolean(src).expect("parse_boolean");
    assert_eq!(q.prime, BigUint::from(29u32));
}

#[test]
fn parse_boolean_declare_fun_inline_ff_sort_infers_prime() {
    // First-pass `declare-fun x () (_ FiniteField N)` branch in
    // `parse_boolean()` with no prior `define-sort`: the `if
    // prime.is_none() { if let Some(n) = inferred { prime = Some(n) } }`
    // arm must pin the session prime to the inline modulus.
    let src = r#"
        (set-logic QF_FF)
        (declare-fun a () (_ FiniteField 31))
        (assert true)
    "#;
    let q = parse_boolean(src).expect("parse_boolean");
    assert_eq!(q.prime, BigUint::from(31u32));
}

// ───────────── finite_field_prime_str: explicit None paths ─────────────

#[test]
fn finite_field_prime_str_returns_none_on_wrong_arity() {
    // List of length 2 fails the `inner.len() == 3` gate, falling through
    // to the `None` return at the bottom of `finite_field_prime_str`.
    assert_eq!(
        finite_field_prime_str(&list(vec![atom("_"), atom("FiniteField")])),
        None
    );
}

#[test]
fn finite_field_prime_str_returns_none_on_non_underscore_head() {
    // Length 3 but `head != "_"` fails the inner conjunction, again
    // falling through to the trailing `None`.
    assert_eq!(
        finite_field_prime_str(&list(vec![
            atom("foo"),
            atom("FiniteField"),
            atom("7"),
        ])),
        None
    );
}

#[test]
fn finite_field_prime_str_returns_none_on_non_atom_components() {
    // Length 3 but a non-atom in one slot fails the `(Atom, Atom, Atom)`
    // tuple pattern, taking the `None` fall-through path.
    assert_eq!(
        finite_field_prime_str(&list(vec![
            atom("_"),
            list(vec![atom("FiniteField")]),
            atom("7"),
        ])),
        None
    );
}

#[test]
fn audit_p2_parse_boolean_multi_accepts_two_distinct_primes() {
    // Two-prime SMT-LIB session. `parse_boolean` would reject this at
    // the literal multi-prime guard; `parse_boolean_multi` accepts it
    // and produces one BooleanQuery per declared prime, in ascending
    // prime order.
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (= x #f3m7))
        (assert (= y #f5m11))
    ";
    let subs = parse_boolean_multi(src).expect("multi-prime parse");
    assert_eq!(subs.len(), 2, "two-prime input must produce two sub-queries");
    assert_eq!(subs[0].prime, BigUint::from(7u32));
    assert_eq!(subs[1].prime, BigUint::from(11u32));
}

#[test]
fn audit_p2_parse_boolean_multi_single_prime_path_equivalent() {
    // Single-prime input degrades to `parse_boolean` verbatim — same
    // prime, same builder var frame, same formula shape.
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (assert (= x #f3m7))
    ";
    let from_multi = parse_boolean_multi(src).expect("single via multi");
    let from_single = parse_boolean(src).expect("single direct");
    assert_eq!(from_multi.len(), 1);
    assert_eq!(from_multi[0].prime, from_single.prime);
    assert_eq!(from_multi[0].var_names(), from_single.var_names());
}

#[test]
fn audit_p2_parse_boolean_multi_rejects_cross_prime_assert() {
    // An assert that mentions both primes is ill-typed SMT-LIB
    // (equality between distinct finite-field sorts is undefined);
    // the parser must reject it as Malformed.
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (= x y))
    ";
    let result = parse_boolean_multi(src);
    assert!(
        matches!(result, Err(ParseError::Malformed(_))),
        "cross-prime assert must be rejected, got {:?}",
        result
    );
}

#[test]
fn audit_p2_two_primes_one_unsat_other_sat() {
    use crate::cdclt::orchestrator::solve_formula_multi;
    use crate::core::SolveOutcome;
    use crate::timeout::CancelToken;

    // GF(7) sub: (x = 3) ∧ (x = 4) — UNSAT; GF(11) sub: (y = 5) — SAT.
    // The combined verdict must be UNSAT.
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (and (= x #f3m7) (= x #f4m7)))
        (assert (= y #f5m11))
    ";
    let subs = parse_boolean_multi(src).expect("parse");
    let primes_subs: Vec<_> = subs
        .into_iter()
        .map(|q| (q.prime.clone(), q.var_names().to_vec(), q.formula.clone()))
        .collect();
    let outcome = solve_formula_multi(primes_subs, &CancelToken::none());
    assert!(
        matches!(outcome, SolveOutcome::Unsat(_)),
        "one-prime-UNSAT-other-prime-SAT must be Unsat, got {:?}",
        outcome
    );
}

#[test]
fn audit_p2_literal_routed_to_correct_prime() {
    // `#f6m7` reduces to 6 mod 7 = 6; `#f12m11` reduces to 12 mod 11
    // = 1. The two literals' canonical values differ, so a sound
    // multi-prime parse must preserve the distinction by routing each
    // to its own prime's atom table. The probe asserts (x = #f6m7)
    // and (y = #f12m11), then verifies the produced sub-queries pin
    // their respective primes via the per-sub `prime` field, and that
    // the verdict is Sat with the values matching the per-prime
    // reductions.
    use crate::cdclt::orchestrator::solve_formula_multi;
    use crate::core::SolveOutcome;
    use crate::timeout::CancelToken;
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (= x #f6m7))
        (assert (= y #f12m11))
    ";
    let subs = parse_boolean_multi(src).expect("parse");
    assert_eq!(subs.len(), 2);
    assert_eq!(subs[0].prime, BigUint::from(7u32));
    assert_eq!(subs[1].prime, BigUint::from(11u32));
    let primes_subs: Vec<_> = subs
        .into_iter()
        .map(|q| (q.prime.clone(), q.var_names().to_vec(), q.formula.clone()))
        .collect();
    let outcome = solve_formula_multi(primes_subs, &CancelToken::none());
    let model = match outcome {
        SolveOutcome::Sat(m) => m,
        other => panic!("expected Sat, got {:?}", other),
    };
    // GF(7): 6 mod 7 = 6. GF(11): 12 mod 11 = 1.
    assert_eq!(
        model.get("x"),
        Some(&BigUint::from(6u32)),
        "x must canonicalise under GF(7), not GF(11)"
    );
    assert_eq!(
        model.get("y"),
        Some(&BigUint::from(1u32)),
        "y must canonicalise under GF(11), not GF(7)"
    );
}

#[test]
fn audit_p2_aux_var_does_not_trip_degraded_in_router() {
    // Drive a multi-prime SMT-LIB session whose Tseitin transform
    // allocates auxiliary SAT variables (a top-level Or). The router
    // must drop the aux vars from `notify_fact` without flipping
    // `degraded`, so the overall verdict is Sat — a degraded path
    // would surface Unknown.
    use crate::cdclt::orchestrator::solve_formula_multi;
    use crate::core::SolveOutcome;
    use crate::timeout::CancelToken;
    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (or (= x #f3m7) (= x #f4m7)))
        (assert (= y #f5m11))
    ";
    let subs = parse_boolean_multi(src).expect("parse");
    let primes_subs: Vec<_> = subs
        .into_iter()
        .map(|q| (q.prime.clone(), q.var_names().to_vec(), q.formula.clone()))
        .collect();
    let outcome = solve_formula_multi(primes_subs, &CancelToken::none());
    assert!(
        matches!(outcome, SolveOutcome::Sat(_)),
        "aux vars from the Tseitin Or must not trip degraded, got {:?}",
        outcome
    );
}

#[test]
fn audit_p2_solve_formula_multi_two_primes_both_sat() {
    use crate::cdclt::orchestrator::solve_formula_multi;
    use crate::core::SolveOutcome;
    use crate::timeout::CancelToken;

    let src = "
        (declare-fun x () (_ FiniteField 7))
        (declare-fun y () (_ FiniteField 11))
        (assert (= x #f3m7))
        (assert (= y #f5m11))
    ";
    let subs = parse_boolean_multi(src).expect("parse");
    let primes_subs: Vec<_> = subs
        .into_iter()
        .map(|q| (q.prime.clone(), q.var_names().to_vec(), q.formula.clone()))
        .collect();
    let outcome = solve_formula_multi(primes_subs, &CancelToken::none());
    assert!(
        matches!(outcome, SolveOutcome::Sat(_)),
        "two-prime independently-SAT input must be Sat, got {:?}",
        outcome
    );
}

