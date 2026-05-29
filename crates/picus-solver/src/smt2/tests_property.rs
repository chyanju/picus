//! Spec-driven property tests for the SMT-LIB v2 parser + FF algebra.
//!
//! Each property is stated against an external SMT-LIB v2 / finite-field
//! invariant before computing the expected value, then cross-checked
//! against the parser's `build_poly_with_ctx` / `parse` / `parse_boolean`
//! output via an independent polynomial evaluator.

use super::*;

/// Build a `ParseCtx` with the given prime, declared vars, and macros.
/// Duplicated from `tests.rs` so this sibling test module is self-contained.
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

/// Independent polynomial evaluator: maps every (idx -> value) and
/// returns `sum_i coeff_i * prod_j x_j^e_j  (mod prime)`. Pure math —
/// used as the reference oracle for `build_poly` outputs.
fn eval_poly(poly: &[PolyTerm], assign: &HashMap<VarIdx, BigUint>, prime: &BigUint) -> BigUint {
    let mut acc = BigUint::zero();
    for t in poly {
        let mut term = t.coeff.clone() % prime;
        for &(idx, exp) in &t.vars {
            let v = assign.get(&idx).cloned().unwrap_or_else(BigUint::zero);
            for _ in 0..exp {
                term = (&term * &v) % prime;
            }
        }
        acc = (&acc + &term) % prime;
    }
    acc
}

/// Build a `ParseCtx` with declared FF variables `xs` under `prime`,
/// then build the polynomial for the given source fragment. Returns
/// the polynomial plus a map var-name -> assigned VarIdx for the
/// evaluator.
fn build_poly_from_src(
    src: &str,
    prime: u32,
    xs: &[&str],
) -> (Polynomial, HashMap<String, VarIdx>) {
    let mut ctx = mk_ctx(prime, &xs.iter().map(|n| (*n, VarSort::Ff)).collect::<Vec<_>>(), vec![]);
    // Pre-intern in declaration order so the var indices are stable.
    let mut name_to_idx: HashMap<String, VarIdx> = HashMap::new();
    for n in xs {
        let i = ctx.builder.var(n);
        name_to_idx.insert((*n).into(), i);
    }
    let toks = tokenize(src);
    let sexprs = parse_sexprs(&toks).expect("parse");
    assert_eq!(sexprs.len(), 1, "expected single sexpr in src");
    let p = build_poly_with_ctx(&sexprs[0], &mut ctx).expect("build_poly_with_ctx ok");
    (p, name_to_idx)
}

// ────────── Algebraic identities through build_poly_with_ctx ──────────
//
// SPEC: Any algebraic identity that holds in GF(p) must hold pointwise
// after the parser builds the LHS and RHS polynomials — for every
// assignment of the free vars, evaluating LHS == evaluating RHS.

/// SPEC: a + 0 = a  (additive identity).
#[test]
fn prop_ff_add_with_zero_is_identity() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (lhs, names) = build_poly_from_src("(ff.add x ff0)", prime, &["x"]);
    let x_idx = names["x"];
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        let got = eval_poly(&lhs, &env, &prime_big);
        let expected = BigUint::from(v); // identity
        assert_eq!(got, expected, "(ff.add x 0)|x={} != {}", v, v);
    }
}

/// SPEC: a * 1 = a  (multiplicative identity).
#[test]
fn prop_ff_mul_with_one_is_identity() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (lhs, names) = build_poly_from_src("(ff.mul x ff1)", prime, &["x"]);
    let x_idx = names["x"];
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        assert_eq!(eval_poly(&lhs, &env, &prime_big), BigUint::from(v));
    }
}

/// SPEC: a * 0 = 0  (multiplicative absorption).
#[test]
fn prop_ff_mul_with_zero_is_zero() {
    let prime = 11u32;
    let prime_big = BigUint::from(prime);
    let (lhs, names) = build_poly_from_src("(ff.mul x ff0)", prime, &["x"]);
    let x_idx = names["x"];
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        assert_eq!(
            eval_poly(&lhs, &env, &prime_big),
            BigUint::zero(),
            "(ff.mul x 0)|x={} != 0",
            v
        );
    }
}

/// SPEC: a + (-a) = 0  (additive inverse).
#[test]
fn prop_ff_add_neg_is_zero() {
    let prime = 13u32;
    let prime_big = BigUint::from(prime);
    let (lhs, names) = build_poly_from_src("(ff.add x (ff.neg x))", prime, &["x"]);
    let x_idx = names["x"];
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        assert_eq!(eval_poly(&lhs, &env, &prime_big), BigUint::zero());
    }
}

/// SPEC: -(-a) = a  (involution of additive negation).
#[test]
fn prop_ff_neg_involution() {
    let prime = 13u32;
    let prime_big = BigUint::from(prime);
    let (lhs, names) = build_poly_from_src("(ff.neg (ff.neg x))", prime, &["x"]);
    let x_idx = names["x"];
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        assert_eq!(eval_poly(&lhs, &env, &prime_big), BigUint::from(v));
    }
}

/// SPEC: (a + b) + c = a + (b + c)  (associativity of addition).
#[test]
fn prop_ff_add_is_associative() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (lhs, n_l) = build_poly_from_src("(ff.add (ff.add a b) c)", prime, &["a", "b", "c"]);
    let (rhs, n_r) = build_poly_from_src("(ff.add a (ff.add b c))", prime, &["a", "b", "c"]);
    // Use the LHS context's indices, then look up the RHS indices via
    // its returned name table.
    for av in 0..prime {
        for bv in 0..prime {
            for cv in 0..prime {
                let mut env_l = HashMap::new();
                env_l.insert(n_l["a"], BigUint::from(av));
                env_l.insert(n_l["b"], BigUint::from(bv));
                env_l.insert(n_l["c"], BigUint::from(cv));
                let mut env_r = HashMap::new();
                env_r.insert(n_r["a"], BigUint::from(av));
                env_r.insert(n_r["b"], BigUint::from(bv));
                env_r.insert(n_r["c"], BigUint::from(cv));
                assert_eq!(
                    eval_poly(&lhs, &env_l, &prime_big),
                    eval_poly(&rhs, &env_r, &prime_big)
                );
            }
        }
    }
}

/// SPEC: a * (b + c) = a*b + a*c  (left-distributivity).
#[test]
fn prop_ff_mul_distributes_over_add() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (lhs, n_l) = build_poly_from_src("(ff.mul a (ff.add b c))", prime, &["a", "b", "c"]);
    let (rhs, n_r) = build_poly_from_src(
        "(ff.add (ff.mul a b) (ff.mul a c))",
        prime,
        &["a", "b", "c"],
    );
    for av in 0..prime {
        for bv in 0..prime {
            for cv in 0..prime {
                let mut env_l = HashMap::new();
                env_l.insert(n_l["a"], BigUint::from(av));
                env_l.insert(n_l["b"], BigUint::from(bv));
                env_l.insert(n_l["c"], BigUint::from(cv));
                let mut env_r = HashMap::new();
                env_r.insert(n_r["a"], BigUint::from(av));
                env_r.insert(n_r["b"], BigUint::from(bv));
                env_r.insert(n_r["c"], BigUint::from(cv));
                assert_eq!(
                    eval_poly(&lhs, &env_l, &prime_big),
                    eval_poly(&rhs, &env_r, &prime_big)
                );
            }
        }
    }
}

/// SPEC: a * b = b * a  (commutativity of multiplication).
#[test]
fn prop_ff_mul_is_commutative() {
    let prime = 11u32;
    let prime_big = BigUint::from(prime);
    let (lhs, n_l) = build_poly_from_src("(ff.mul a b)", prime, &["a", "b"]);
    let (rhs, n_r) = build_poly_from_src("(ff.mul b a)", prime, &["a", "b"]);
    for av in 0..prime {
        for bv in 0..prime {
            let mut env_l = HashMap::new();
            env_l.insert(n_l["a"], BigUint::from(av));
            env_l.insert(n_l["b"], BigUint::from(bv));
            let mut env_r = HashMap::new();
            env_r.insert(n_r["a"], BigUint::from(av));
            env_r.insert(n_r["b"], BigUint::from(bv));
            assert_eq!(
                eval_poly(&lhs, &env_l, &prime_big),
                eval_poly(&rhs, &env_r, &prime_big)
            );
        }
    }
}

/// SPEC: Empty `(ff.add)` is the additive identity 0 (universal property
/// of the empty sum in a ring).
#[test]
fn prop_empty_ff_add_evaluates_to_zero() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, _) = build_poly_from_src("(ff.add)", prime, &[]);
    assert_eq!(eval_poly(&p, &HashMap::new(), &prime_big), BigUint::zero());
}

/// SPEC: Empty `(ff.mul)` is the multiplicative identity 1 (universal
/// property of the empty product in a ring with 1).
#[test]
fn prop_empty_ff_mul_evaluates_to_one() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, _) = build_poly_from_src("(ff.mul)", prime, &[]);
    assert_eq!(eval_poly(&p, &HashMap::new(), &prime_big), BigUint::from(1u32));
}

/// SPEC: `(ff.add a)` (single arg) = a, i.e. unary `+` is the identity.
#[test]
fn prop_unary_ff_add_is_identity() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, names) = build_poly_from_src("(ff.add x)", prime, &["x"]);
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(names["x"], BigUint::from(v));
        assert_eq!(eval_poly(&p, &env, &prime_big), BigUint::from(v));
    }
}

/// SPEC: `(ff.mul a)` (single arg) = a, i.e. unary `*` is the identity.
#[test]
fn prop_unary_ff_mul_is_identity() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, names) = build_poly_from_src("(ff.mul x)", prime, &["x"]);
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(names["x"], BigUint::from(v));
        assert_eq!(eval_poly(&p, &env, &prime_big), BigUint::from(v));
    }
}

// ────────── bit-sum spec (recurring bug hazard) ──────────

/// SPEC: `(ff.bitsum b_0 b_1 ... b_{n-1})` equals
/// `sum_i 2^i * b_i  (mod prime)`. Exact powers of 2 — not arbitrary
/// coefficients. Tested by evaluating against every binary assignment
/// and comparing to the canonical integer the bits encode.
#[test]
fn prop_ff_bitsum_is_weighted_powers_of_two() {
    let prime = 257u32; // > 2^8 so no wrap on 8 bits
    let prime_big = BigUint::from(prime);
    let (p, names) = build_poly_from_src(
        "(ff.bitsum b0 b1 b2 b3 b4 b5 b6 b7)",
        prime,
        &["b0", "b1", "b2", "b3", "b4", "b5", "b6", "b7"],
    );
    for n in 0u32..256u32 {
        let mut env = HashMap::new();
        for i in 0..8 {
            let bit = (n >> i) & 1;
            env.insert(names[&format!("b{}", i)], BigUint::from(bit));
        }
        let got = eval_poly(&p, &env, &prime_big);
        assert_eq!(
            got,
            BigUint::from(n),
            "bitsum decoded {} but n was {}",
            got,
            n
        );
    }
}

/// SPEC: `(ff.bitsum a)` (single arg) is just `a` (weight = 2^0 = 1).
#[test]
fn prop_ff_bitsum_unary_is_weight_one() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, names) = build_poly_from_src("(ff.bitsum x)", prime, &["x"]);
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(names["x"], BigUint::from(v));
        assert_eq!(eval_poly(&p, &env, &prime_big), BigUint::from(v));
    }
}

/// SPEC: Empty `(ff.bitsum)` is the empty sum = 0.
#[test]
fn prop_empty_ff_bitsum_is_zero() {
    let prime = 7u32;
    let prime_big = BigUint::from(prime);
    let (p, _) = build_poly_from_src("(ff.bitsum)", prime, &[]);
    assert_eq!(eval_poly(&p, &HashMap::new(), &prime_big), BigUint::zero());
}

// ────────── parse_ff_const spec ──────────

/// SPEC: `ff{N}` denotes the integer N reduced mod p for every prime p
/// and every nonneg integer N. (SMT-LIB QF_FF literal spec.)
#[test]
fn prop_parse_ff_const_unsigned_is_n_mod_p() {
    // Sweep several primes (small + medium) and several Ns.
    for &p in &[2u32, 3, 5, 7, 11, 13, 31, 257] {
        let prime = BigUint::from(p);
        for n in 0u32..=300 {
            let sym = format!("ff{}", n);
            let got = parse_ff_const(&sym, &prime).expect("ff-const");
            let expected = BigUint::from(n % p);
            assert_eq!(got, expected, "ff{} mod {} expected {}", n, p, expected);
        }
    }
}

/// SPEC: `ff-{N}` for N > 0 denotes `(p - (N mod p)) mod p`. For N = 0
/// it is 0. (SMT-LIB QF_FF negative-literal convention.)
#[test]
fn prop_parse_ff_const_negative_is_p_minus_n_mod_p() {
    for &p in &[3u32, 5, 7, 11, 13, 31] {
        let prime = BigUint::from(p);
        for n in 0u32..=100 {
            let sym = format!("ff-{}", n);
            let got = parse_ff_const(&sym, &prime).expect("ff-const");
            let n_mod = n % p;
            let expected = if n_mod == 0 {
                BigUint::zero()
            } else {
                BigUint::from(p - n_mod)
            };
            assert_eq!(got, expected, "ff-{} in GF({}) expected {}", n, p, expected);
        }
    }
}

/// SPEC: `(ff-N + ffN) mod p = 0` for every prime p and N. (Additive
/// inverse — defines what the negative literal MEANS.)
#[test]
fn prop_parse_ff_const_negative_is_additive_inverse() {
    for &p in &[2u32, 3, 5, 7, 11, 13] {
        let prime = BigUint::from(p);
        for n in 0u32..=50 {
            let pos = parse_ff_const(&format!("ff{}", n), &prime).expect("ff+");
            let neg = parse_ff_const(&format!("ff-{}", n), &prime).expect("ff-");
            assert_eq!((pos + neg) % &prime, BigUint::zero());
        }
    }
}

/// SPEC: `#f{N}m{p}` with matching modulus denotes N mod p, and is
/// rejected (None) when the literal-side modulus disagrees with the
/// session prime. (SMT-LIB v2 `#f` syntax — literal self-tags its field.)
#[test]
fn prop_parse_ff_const_hash_form_rejects_mismatched_prime() {
    let prime7 = BigUint::from(7u32);
    // Matching: works.
    assert_eq!(parse_ff_const("#f3m7", &prime7), Some(BigUint::from(3u32)));
    // Mismatching modulus → None (silent re-encoding would be unsound).
    assert_eq!(parse_ff_const("#f3m11", &prime7), None);
    assert_eq!(parse_ff_const("#f3m13", &prime7), None);
    // Differently-but-equivalently sized N is still rejected when m
    // doesn't match.
    assert_eq!(parse_ff_const("#f0m11", &prime7), None);
}

/// ROUND-TRIP: `format_value(v, Ff, Some(p))` produces `#f{v}m{p}`
/// (per session.rs format spec), and feeding that back into
/// `parse_ff_const` under the same prime recovers v (when v < p).
#[test]
fn prop_format_then_parse_ff_const_round_trips() {
    for &p in &[2u32, 3, 5, 7, 11, 13, 257] {
        let prime = BigUint::from(p);
        for v in 0..p {
            // The session's format is documented as `#f{val}m{prime}`.
            let s = format!("#f{}m{}", v, p);
            let got = parse_ff_const(&s, &prime).expect("parse");
            assert_eq!(got, BigUint::from(v));
        }
    }
}

// ────────── Conjunctive `parse` semantics ──────────

/// SPEC: For an assertion `(= LHS RHS)`, the parser emits ONE equality
/// polynomial whose semantic value is `LHS - RHS (mod prime)`. So under
/// any assignment where LHS == RHS, the polynomial evaluates to 0; and
/// vice versa where it evaluates to 0, LHS == RHS. We test the
/// SAT-witness direction: `(= x ffk)` evaluated at x=k yields 0.
#[test]
fn prop_parse_eq_polynomial_evaluates_to_zero_at_solution() {
    let p = 7u32;
    let prime = BigUint::from(p);
    for k in 0..p {
        let src = format!(
            "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= x ff{}))",
            p, k
        );
        let cs = parse(&src).expect("parse");
        assert_eq!(cs.equalities.len(), 1);
        // x is the only variable.
        let x_idx = cs
            .var_names
            .iter()
            .position(|n| n == "x")
            .expect("x interned") as VarIdx;
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(k));
        assert_eq!(
            eval_poly(&cs.equalities[0], &env, &prime),
            BigUint::zero(),
            "(= x ff{}) at x={} should be 0",
            k,
            k
        );
    }
}

/// SPEC: For `(= LHS RHS)`, evaluating the polynomial at any
/// non-solution assignment yields a NONZERO value (otherwise the parser
/// would silently equate distinct field elements). Together with the
/// previous test, this characterises `LHS - RHS == 0` exactly.
#[test]
fn prop_parse_eq_polynomial_nonzero_at_non_solution() {
    let p = 7u32;
    let prime = BigUint::from(p);
    let src = format!(
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= x ff3))",
        p
    );
    let cs = parse(&src).expect("parse");
    let x_idx = cs
        .var_names
        .iter()
        .position(|n| n == "x")
        .expect("x interned") as VarIdx;
    for k in 0..p {
        if k == 3 {
            continue;
        }
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(k));
        let got = eval_poly(&cs.equalities[0], &env, &prime);
        assert!(!got.is_zero(), "(= x 3) at x={} should be != 0", k);
    }
}

/// SPEC: Tautological equalities — `(= (ff.add x ff0) x)` and `(= x x)`
/// — encode a polynomial identically zero in GF(p)[x]. Every retained
/// equality in the parsed CS must therefore evaluate to 0 at every
/// assignment. (rewriter may prune the empty-after-normalization
/// equality; both states satisfy the universal-zero property.)
#[test]
fn prop_parse_eq_zero_polynomial_for_tautology() {
    let p = 11u32;
    let prime = BigUint::from(p);
    let src_a = format!(
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= (ff.add x ff0) x))",
        p
    );
    let src_b = format!(
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= x x))",
        p
    );
    let cs_a = parse(&src_a).expect("parse a");
    let cs_b = parse(&src_b).expect("parse b");
    let xa = cs_a.var_names.iter().position(|n| n == "x").unwrap_or(0) as VarIdx;
    let xb = cs_b.var_names.iter().position(|n| n == "x").unwrap_or(0) as VarIdx;
    for v in 0..p {
        let mut env_a = HashMap::new();
        env_a.insert(xa, BigUint::from(v));
        let mut env_b = HashMap::new();
        env_b.insert(xb, BigUint::from(v));
        for eq in &cs_a.equalities {
            assert_eq!(eval_poly(eq, &env_a, &prime), BigUint::zero());
        }
        for eq in &cs_b.equalities {
            assert_eq!(eval_poly(eq, &env_b, &prime), BigUint::zero());
        }
    }
}

// ────────── Edge-prime invariants (recurring hazard class) ──────────

/// SPEC: GF(2) has only {0, 1}. `(ff.add x x) = 0` for any x in GF(2)
/// (characteristic 2: a + a = 2a = 0).
#[test]
fn prop_gf2_self_addition_is_zero() {
    let prime = 2u32;
    let prime_big = BigUint::from(prime);
    let (p, names) = build_poly_from_src("(ff.add x x)", prime, &["x"]);
    for v in 0..prime {
        let mut env = HashMap::new();
        env.insert(names["x"], BigUint::from(v));
        assert_eq!(eval_poly(&p, &env, &prime_big), BigUint::zero());
    }
}

/// SPEC: In GF(p), -1 ≡ p - 1. So `(ff.neg ff1) = ff(p-1)` (in value).
#[test]
fn prop_ff_neg_of_one_is_p_minus_one() {
    for &p in &[2u32, 3, 5, 7, 11, 13, 31] {
        let prime = BigUint::from(p);
        let (poly, _) = build_poly_from_src("(ff.neg ff1)", p, &[]);
        let got = eval_poly(&poly, &HashMap::new(), &prime);
        // In GF(2), -1 ≡ 1; in GF(p>2), -1 ≡ p - 1.
        let expected = (BigUint::from(p) - BigUint::from(1u32)) % &prime;
        assert_eq!(got, expected, "(ff.neg 1) in GF({}) was {}", p, got);
    }
}

/// SPEC: Negation under a big BN128-class prime — same algebraic
/// identity (a + (-a) = 0) must hold. We pick a representative big
/// prime (Mersenne 2^61-1, prime).
#[test]
fn prop_big_prime_negation_identity() {
    let big = BigUint::parse_bytes(b"2305843009213693951", 10).expect("bigp"); // 2^61 - 1
    let mut vars = HashMap::new();
    vars.insert("x".to_string(), VarSort::Ff);
    let mut ctx = ParseCtx {
        prime: big.clone(),
        vars,
        macros: HashMap::new(),
        next_ite_skolem: 0,
        side_constraints: Vec::new(),
        builder: ConstraintSystemBuilder::new(big.clone()),
        expansion_depth: 0,
    };
    let x_idx = ctx.builder.var("x");
    let toks = tokenize("(ff.add x (ff.neg x))");
    let sxs = parse_sexprs(&toks).unwrap();
    let poly = build_poly_with_ctx(&sxs[0], &mut ctx).expect("build");
    // Try several large values.
    for v in [0u64, 1, 12345, 999999999, (1u64 << 60)] {
        let mut env = HashMap::new();
        env.insert(x_idx, BigUint::from(v));
        assert_eq!(eval_poly(&poly, &env, &big), BigUint::zero());
    }
}

// ────────── parse-then-reparse round-trip via session ──────────

/// ROUND-TRIP / DETERMINISM: Two independent `parse` calls on the same
/// source produce equal `ConstraintSystem`s (modulo possible Vec layout
/// differences — we compare prime, var_names, equalities count, and
/// per-equality semantic evaluation).
#[test]
fn prop_parse_is_deterministic_across_two_calls() {
    let src = r#"
        (set-logic QF_FF)
        (define-sort F () (_ FiniteField 11))
        (declare-fun x () F)
        (declare-fun y () F)
        (assert (= (ff.add x y) ff5))
        (assert (= (ff.mul x y) ff3))
        (check-sat)
    "#;
    let a = parse(src).expect("a");
    let b = parse(src).expect("b");
    assert_eq!(a.prime, b.prime);
    assert_eq!(a.var_names, b.var_names);
    assert_eq!(a.equalities.len(), b.equalities.len());
    let prime = a.prime.clone();
    // Compare semantically: evaluate every equality at random points.
    for xv in 0..11u32 {
        for yv in 0..11u32 {
            let xi = a.var_names.iter().position(|n| n == "x").unwrap() as VarIdx;
            let yi = a.var_names.iter().position(|n| n == "y").unwrap() as VarIdx;
            let mut env = HashMap::new();
            env.insert(xi, BigUint::from(xv));
            env.insert(yi, BigUint::from(yv));
            for (e_a, e_b) in a.equalities.iter().zip(b.equalities.iter()) {
                assert_eq!(eval_poly(e_a, &env, &prime), eval_poly(e_b, &env, &prime));
            }
        }
    }
}

/// SPEC: `parse` and `parse_boolean` agree on the underlying prime for a
/// QF_FF script that lies in the conjunctive fragment. (Both pipelines
/// derive the prime from the SAME inputs — sort decls + literal hints —
/// so the outcome MUST coincide.)
#[test]
fn prop_parse_and_parse_boolean_agree_on_prime() {
    for src in [
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField 5)) (assert (= x ff2))",
        "(set-logic QF_FF) (define-sort F () (_ FiniteField 13)) (declare-fun y () F) (assert (= y ff7))",
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField 7)) (assert (= x #f3m7))",
    ] {
        let a = parse(src).expect("parse");
        let b = parse_boolean(src).expect("parse_boolean");
        assert_eq!(a.prime, b.prime, "prime mismatch for {:?}", src);
    }
}

// ────────── Whitespace/comment invariance of `parse` ──────────

/// SPEC: Comments and whitespace are lexical noise per SMT-LIB v2 §3.1.
/// Two scripts that differ only in comments + extra whitespace must
/// produce the SAME ConstraintSystem (prime, var_names, # of
/// equalities). (Tokenization invariance lifts to parser invariance.)
#[test]
fn prop_parse_is_comment_and_whitespace_invariant() {
    let bare = "(set-logic QF_FF) (declare-fun x () (_ FiniteField 7)) (assert (= x ff3))";
    let noisy = "\n  ; header comment\n(set-logic QF_FF) ; logic\n  (declare-fun x () (_ FiniteField 7))\n  ; another\n  (assert (= x ff3))\n;trailing\n";
    let a = parse(bare).expect("a");
    let b = parse(noisy).expect("b");
    assert_eq!(a.prime, b.prime);
    assert_eq!(a.var_names, b.var_names);
    assert_eq!(a.equalities.len(), b.equalities.len());
    assert_eq!(a.disequalities.len(), b.disequalities.len());
    assert_eq!(a.assignments.len(), b.assignments.len());
}

// ────────── Macro / define-fun expansion vs inlined ──────────

/// SPEC: `(define-fun f ((x F)) F body)` followed by `(f e)` MUST be
/// semantically equivalent to a fresh-substitution of `body[x := e]`.
/// Built around `(ff.add x ff0)` which evaluates to x; the body's
/// polynomial must evaluate identically to the inlined version under
/// any assignment to e.
#[test]
fn prop_define_fun_expansion_matches_inlined() {
    let p = 7u32;
    let prime = BigUint::from(p);
    let src_macro = format!(
        "(set-logic QF_FF)
         (define-sort F () (_ FiniteField {}))
         (define-fun f ((y F)) F (ff.add y ff0))
         (declare-fun x () F)
         (assert (= (f x) ff3))",
        p
    );
    let src_inline = format!(
        "(set-logic QF_FF)
         (define-sort F () (_ FiniteField {}))
         (declare-fun x () F)
         (assert (= (ff.add x ff0) ff3))",
        p
    );
    let qa = parse_boolean(&src_macro).expect("macro");
    let qb = parse_boolean(&src_inline).expect("inline");
    assert_eq!(qa.prime, qb.prime);
    // Both queries must have exactly one declared FF variable "x" plus
    // possibly synthetic skolems — but our bodies introduce none, so
    // the var_names lists should agree.
    let xa = qa.var_names().iter().position(|n| n == "x").expect("xa");
    let xb = qb.var_names().iter().position(|n| n == "x").expect("xb");
    // Now extract the formula's literal `Eq` polynomial pair and
    // semantically compare under every x value.
    fn first_eq(f: &Formula) -> Option<(&Polynomial, &Polynomial)> {
        match f {
            Formula::Lit(Literal::Eq(a, b)) => Some((a, b)),
            Formula::And(fs) => fs.iter().find_map(first_eq),
            _ => None,
        }
    }
    let (la, ra) = first_eq(&qa.formula).expect("eq in macro");
    let (lb, rb) = first_eq(&qb.formula).expect("eq in inline");
    for v in 0..p {
        let mut env_a = HashMap::new();
        env_a.insert(xa as VarIdx, BigUint::from(v));
        let mut env_b = HashMap::new();
        env_b.insert(xb as VarIdx, BigUint::from(v));
        // Each side evaluates as (la - ra) at v == 0 iff lhs = rhs.
        let diff_a = (eval_poly(la, &env_a, &prime) + &prime
            - eval_poly(ra, &env_a, &prime))
            % &prime;
        let diff_b = (eval_poly(lb, &env_b, &prime) + &prime
            - eval_poly(rb, &env_b, &prime))
            % &prime;
        assert_eq!(diff_a, diff_b);
    }
}

// ────────── Conjunctive parser: tautological `(= ff0 ff0)` ──────────

/// SPEC: `(= ffN ffN)` is a tautology — the equality polynomial is
/// identically zero modulo prime. After post-parse normalization
/// (rewrite_system), an identically-zero equality MUST evaluate to 0
/// at every assignment (regardless of whether it's been pruned out of
/// the equality list by normalization or retained as an empty
/// polynomial); in either case, the conjunction of equalities is
/// satisfied at every assignment.
#[test]
fn prop_parse_constant_equality_is_zero_polynomial() {
    let p = 11u32;
    let prime = BigUint::from(p);
    let src = format!(
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= ff5 ff5))",
        p
    );
    let cs = parse(&src).expect("parse");
    // Spec: every retained equality (after normalization) must
    // evaluate to 0 at every assignment we test, since the original
    // assertion `(= ff5 ff5)` is a tautology over GF(p).
    let env: HashMap<VarIdx, BigUint> = HashMap::new();
    for eq in &cs.equalities {
        assert_eq!(eval_poly(eq, &env, &prime), BigUint::zero());
    }
}

/// SPEC: `(= ffA ffB)` with A != B (mod p) is a contradiction — the
/// polynomial evaluates to a NONZERO constant under every assignment.
/// (This is a *failure-mode* property: the parser must NOT silently
/// emit a zero polynomial.)
#[test]
fn prop_parse_contradictory_constant_equality_is_nonzero_polynomial() {
    let p = 11u32;
    let prime = BigUint::from(p);
    let src = format!(
        "(set-logic QF_FF) (declare-fun x () (_ FiniteField {})) (assert (= ff5 ff3))",
        p
    );
    let cs = parse(&src).expect("parse");
    let env: HashMap<VarIdx, BigUint> = HashMap::new();
    assert!(!eval_poly(&cs.equalities[0], &env, &prime).is_zero());
}
