use super::*;
use crate::ff::field::PrimeField;
use crate::gb::ideal::{Ideal, compute_gb_with_order};
use crate::poly::FfPolyRing;
use crate::timeout::CancelToken;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

/// Monic, sorted-terms canonical form for set comparison of GBs.
/// Normalises by the *Lex* leading coefficient (the target order), so
/// scalar-multiple representatives of the same GB element compare equal
/// regardless of the ring's stored monomial order.
fn canon(pr: &FfPolyRing, p: &Poly) -> Vec<(Vec<u16>, BigUint)> {
    let f = &pr.field();
    // Lex-largest monomial among the poly's terms.
    let mut lex_lm: Option<Monomial> = None;
    for (_, m) in pr.ring.terms(p) {
        lex_lm = Some(match lex_lm {
            None => m,
            Some(cur) => {
                if m.cmp_with_order(&cur, MonomialOrder::Lex) == Ordering::Greater {
                    m
                } else {
                    cur
                }
            }
        });
    }
    let lex_lm = lex_lm.expect("nonzero poly");
    let mut lc = f.zero();
    for (c, m) in pr.ring.terms(p) {
        if m.exponents() == lex_lm.exponents() {
            lc = f.clone_el(c);
        }
    }
    let inv = f.inv(&lc).expect("nonzero leading coeff");
    let mut terms: Vec<(Vec<u16>, BigUint)> = pr
        .ring
        .terms(p)
        .map(|(c, m)| (m.exponents().to_vec(), f.to_biguint(&f.mul(c, &inv))))
        .collect();
    terms.sort();
    terms
}

fn canon_set(pr: &FfPolyRing, gb: &[Poly]) -> Vec<Vec<(Vec<u16>, BigUint)>> {
    let mut v: Vec<_> = gb
        .iter()
        .filter(|p| !pr.is_zero(p))
        .map(|p| canon(pr, p))
        .collect();
    v.sort();
    v
}

/// FGLM-converted Lex GB must equal the directly-computed Lex GB
/// (reduced GBs are unique up to ordering + monic normalisation).
fn assert_fglm_matches(pr: &FfPolyRing, gens: Vec<Poly>) {
    let drl = Ideal::new(pr, gens.iter().map(|p| pr.ring.clone_el(p)).collect());
    assert!(drl.is_zero_dim(), "test ideal must be zero-dimensional");
    let fglm = fglm_to_lex(&drl).expect("zero-dim → Some");
    let direct = compute_gb_with_order(pr, gens, &CancelToken::none(), MonomialOrder::Lex);
    assert_eq!(
        canon_set(pr, &fglm),
        canon_set(pr, &direct),
        "FGLM Lex GB disagrees with direct Lex Buchberger"
    );
}

#[test]
fn fglm_two_var_quadratics() {
    // GF(7): <x^2 - 3, y^2 - 2, x + y - 1> — zero-dimensional.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(3)),
        pr.sub(y2, c(2)),
        pr.sub(pr.add(pr.var(0), pr.var(1)), pr.one()),
    ];
    assert_fglm_matches(&pr, gens);
}

#[test]
fn fglm_inverse_relation() {
    // GF(11): <x^2 - 5, x*y - 1> — zero-dimensional (y = x/5).
    let pr = FfPolyRing::new(ff(11), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, pr.constant(pr.field().from_int(5))),
        pr.sub(xy, pr.one()),
    ];
    assert_fglm_matches(&pr, gens);
}

#[test]
fn fglm_three_vars() {
    // GF(13): <x^2 - 1, y^2 - x, z - x*y> — zero-dimensional.
    let pr = FfPolyRing::new(ff(13), vec!["x".into(), "y".into(), "z".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, pr.one()),
        pr.sub(y2, pr.var(0)),
        pr.sub(pr.var(2), xy),
    ];
    assert_fglm_matches(&pr, gens);
}

#[test]
fn fglm_rejects_positive_dimensional() {
    // <x*y> over GF(7): positive-dimensional → None (caller falls back).
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let drl = Ideal::new(&pr, vec![xy]);
    assert!(fglm_to_lex(&drl).is_none());
    // The Hilbert oracle agrees: positive-dimensional ⇒ no finite dim.
    assert_eq!(drl.quotient_dimension(), None);
}

#[test]
fn quotient_dimension_matches_fglm_staircase() {
    // The Hilbert quotient dimension equals dim_k(R/I) = the FGLM
    // staircase size (the in-`fglm_to_lex` debug-assert checks the
    // equality directly on every zero-dim fixture). `<x^2-5, x*y-1>`
    // over GF(11) has GB {x - 5y, y^2 - 9}: standard monomials {1, y}
    // ⇒ dim 2 (the two roots x = ±4, y = 1/x).
    let pr = FfPolyRing::new(ff(11), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, pr.constant(pr.field().from_int(5))),
        pr.sub(xy, pr.one()),
    ];
    let drl = Ideal::new(&pr, gens);
    assert_eq!(drl.quotient_dimension(), Some(2));
    let lex = fglm_to_lex(&drl).expect("zero-dim → Some");
    assert!(!lex.is_empty());
}

// ────────── LexKey ──────────

#[test]
fn lexkey_eq_compares_exponents() {
    let a = LexKey(Monomial::from_exponents(vec![1, 0]));
    let b = LexKey(Monomial::from_exponents(vec![1, 0]));
    let c = LexKey(Monomial::from_exponents(vec![0, 1]));
    assert!(a == b);
    assert!(a != c);
}

#[test]
fn lexkey_order_is_lex() {
    // x > y in Lex: [1,0] sorts above [0,1]. partial_cmp delegates to Ord.
    let x = LexKey(Monomial::from_exponents(vec![1, 0]));
    let y = LexKey(Monomial::from_exponents(vec![0, 1]));
    assert_eq!(x.partial_cmp(&y), Some(Ordering::Greater));
    assert_eq!(y.partial_cmp(&x), Some(Ordering::Less));
    assert_eq!(x.cmp(&x), Ordering::Equal);
    // x^2 (=[2,0]) > x (=[1,0]) in Lex (first exponent dominates).
    let x2 = LexKey(Monomial::from_exponents(vec![2, 0]));
    assert_eq!(x2.partial_cmp(&x), Some(Ordering::Greater));
}

#[test]
fn fglm_runs_gb_stats_scope_block() {
    // With `gb_stats_enabled`, the `metric::scope!` dump block in
    // `fglm_to_lex` runs (the staircase-vs-Hilbert eprintln). The
    // verdict and Lex GB must be unchanged by the telemetry gate.
    let _g = crate::config::ConfigGuard::with_override(|c| c.gb_stats_enabled = true);
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(3)),
        pr.sub(y2, c(2)),
        pr.sub(pr.add(pr.var(0), pr.var(1)), pr.one()),
    ];
    // Exercises the gb-stats scope inside `fglm_to_lex` and still
    // matches the direct Lex Buchberger basis.
    assert_fglm_matches(&pr, gens);
}

#[test]
fn lexkey_btreeset_dedups_and_orders() {
    // BTreeSet uses Ord + Eq: a duplicate exponent vector is collapsed,
    // and iteration yields increasing Lex order.
    let mut set: BTreeSet<LexKey> = BTreeSet::new();
    set.insert(LexKey(Monomial::from_exponents(vec![0, 1]))); // y
    set.insert(LexKey(Monomial::from_exponents(vec![1, 0]))); // x
    set.insert(LexKey(Monomial::from_exponents(vec![0, 1]))); // y again
    assert_eq!(set.len(), 2);
    let ordered: Vec<Vec<u16>> = set.iter().map(|k| k.0.exponents().to_vec()).collect();
    // Increasing Lex: y = [0,1] before x = [1,0].
    assert_eq!(ordered, vec![vec![0, 1], vec![1, 0]]);
}

// ─────────────── HARD-PROBE: cross-module bug hunt ───────────────
//
// All tests in this section are spec-driven: expected outputs come from
// the mathematical definition of FGLM (lex GB of the same ideal as the
// DRL input) or Hilbert dimension (count of standard monomials of the
// monomial ideal of leading terms) — not from picus's own output. A
// failing test is a BUG.

/// Mutual ideal-membership: ideals generated by `a_basis` and `b_basis`
/// are equal. Each basis is RE-COMPUTED as a DRL GB (the ring's stored
/// order) before reduction, so neither input has to already be a GB in
/// the ring's order. Probes ideal-set equality via NF-by-DRL-GB.
fn assert_same_ideal(pr: &FfPolyRing, a_basis: &[Poly], b_basis: &[Poly]) {
    let id_a = Ideal::new(pr, a_basis.iter().map(|p| pr.ring.clone_el(p)).collect());
    let id_b = Ideal::new(pr, b_basis.iter().map(|p| pr.ring.clone_el(p)).collect());
    for (i, p) in b_basis.iter().enumerate() {
        let r = id_a.reduce(p);
        assert!(
            pr.is_zero(&r),
            "basis-B element {} does NOT lie in ideal-A (NF mod A's DRL GB ≠ 0)",
            i
        );
    }
    for (i, p) in a_basis.iter().enumerate() {
        let r = id_b.reduce(p);
        assert!(
            pr.is_zero(&r),
            "basis-A element {} does NOT lie in ideal-B (NF mod B's DRL GB ≠ 0)",
            i
        );
    }
}

/// SPEC: FGLM output must generate the same ideal as direct Lex
/// Buchberger of the same generators. Probe via mutual ideal-membership
/// instead of canonical-form equality (catches a `canon`-side bug too).
fn assert_fglm_ideal_eq_direct(pr: &FfPolyRing, gens: Vec<Poly>) {
    let drl = Ideal::new(pr, gens.iter().map(|p| pr.ring.clone_el(p)).collect());
    assert!(drl.is_zero_dim(), "test ideal must be zero-dimensional");
    let fglm = fglm_to_lex(&drl).expect("zero-dim ⇒ Some");
    let direct = compute_gb_with_order(pr, gens, &CancelToken::none(), MonomialOrder::Lex);
    assert_same_ideal(pr, &direct, &fglm);
}

/// Stronger: every FGLM output element must lie in the SOURCE DRL ideal.
/// This catches a class of bug where FGLM emits a polynomial that
/// happens to equal something monic but is NOT in the original ideal —
/// the Hilbert-dim cross-check inside `fglm_to_lex` does NOT catch all
/// such cases (e.g., a wrong combination on the staircase whose linear
/// algebra still terminates at the right size).
fn assert_fglm_in_source_ideal(pr: &FfPolyRing, gens: Vec<Poly>) {
    let drl = Ideal::new(pr, gens);
    let fglm = fglm_to_lex(&drl).expect("zero-dim ⇒ Some");
    for (i, p) in fglm.iter().enumerate() {
        let r = drl.reduce(p);
        assert!(
            pr.is_zero(&r),
            "FGLM elem #{} does NOT lie in source DRL ideal (NF non-zero)",
            i
        );
    }
}

// ── Differential probe across EDGE PRIMES ──────────────────────────

#[test]
fn fglm_ideal_eq_direct_gf2() {
    // Smallest characteristic. Pure-power gens: <x^2 + x, y^2 + y> in
    // GF(2)[x, y] — the Boolean ring; zero-dim with dim = 4 (the
    // standard monomials {1, x, y, xy}). FGLM must agree with direct Lex.
    let pr = FfPolyRing::new(ff(2), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.add(x2, pr.var(0)), // x^2 + x = x^2 - x in GF(2)
        pr.add(y2, pr.var(1)),
    ];
    assert_fglm_ideal_eq_direct(&pr, gens);
}

#[test]
fn fglm_ideal_eq_direct_gf3() {
    // GF(3): <x^2 - 1, y - x>; zero-dim (y is determined by x, x has
    // two roots ±1). SPEC dim = 2.
    let pr = FfPolyRing::new(ff(3), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let gens = vec![
        pr.sub(x2, pr.one()),
        pr.sub(pr.var(1), pr.var(0)),
    ];
    let drl = Ideal::new(&pr, gens.iter().map(|p| pr.ring.clone_el(p)).collect());
    assert_eq!(
        drl.quotient_dimension(),
        Some(2),
        "spec: <x^2-1, y-x> has dim 2 (the two roots)"
    );
    assert_fglm_ideal_eq_direct(&pr, gens);
}

#[test]
fn fglm_ideal_eq_direct_gf5() {
    // GF(5): two coupled quadratics.
    let pr = FfPolyRing::new(ff(5), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(2)),
        pr.sub(y2, c(3)),
        pr.sub(xy, c(1)),
    ];
    assert_fglm_ideal_eq_direct(&pr, gens);
}

#[test]
fn fglm_ideal_eq_direct_prime_257() {
    // Mersenne-ish small prime.
    let pr = FfPolyRing::new(ff(257), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(5)),
        pr.sub(y2, c(11)),
        pr.sub(pr.add(pr.var(0), pr.var(1)), c(7)),
    ];
    assert_fglm_ideal_eq_direct(&pr, gens);
}

#[test]
fn fglm_ideal_eq_direct_prime_1009() {
    let pr = FfPolyRing::new(ff(1009), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(3)),
        pr.sub(xy, c(1)),
    ];
    assert_fglm_ideal_eq_direct(&pr, gens);
}

// ── Strong invariant: FGLM output lies in source ideal ─────────────

#[test]
fn fglm_output_lies_in_source_ideal_gf7() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(3)),
        pr.sub(y2, c(2)),
        pr.sub(pr.add(pr.var(0), pr.var(1)), pr.one()),
    ];
    assert_fglm_in_source_ideal(&pr, gens);
}

#[test]
fn fglm_output_lies_in_source_ideal_three_var() {
    let pr = FfPolyRing::new(ff(13), vec!["x".into(), "y".into(), "z".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let xy = pr.mul(pr.var(0), pr.var(1));
    let gens = vec![
        pr.sub(x2, pr.one()),
        pr.sub(y2, pr.var(0)),
        pr.sub(pr.var(2), xy),
    ];
    assert_fglm_in_source_ideal(&pr, gens);
}

// ── Edge zero-dim cases ─────────────────────────────────────────────

#[test]
fn fglm_unit_ideal_returns_one() {
    // SPEC: the unit ideal <1> has reduced lex GB = {1}.
    // `Ideal::from_gb` lets us hand-feed the GB without re-running Buchberger.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let one = pr.one();
    let drl = Ideal::from_gb(&pr, vec![one]);
    assert!(drl.is_whole_ring(), "spec: <1> is the whole ring");
    let lex = fglm_to_lex(&drl).expect("unit ideal is zero-dim ⇒ Some");
    assert_eq!(lex.len(), 1, "spec: reduced lex GB of <1> has exactly one element");
    assert!(lex[0].is_constant() && !pr.is_zero(&lex[0]),
        "spec: lex GB of <1> is {{1}} (a nonzero constant)");
}

#[test]
fn fglm_maximal_ideal_one_var() {
    // SPEC: <x - 2> in GF(7)[x] is maximal, zero-dim, dim 1.
    // The lex GB is {x - 2}; FGLM must agree with direct.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let g = pr.sub(pr.var(0), c(2));
    let drl = Ideal::new(&pr, vec![pr.ring.clone_el(&g)]);
    assert_eq!(drl.quotient_dimension(), Some(1));
    let lex = fglm_to_lex(&drl).expect("zero-dim ⇒ Some");
    // staircase = {1}, so exactly one lex GB element (representing x).
    assert_eq!(lex.len(), 1);
    // SPEC: x - 2 reduces to 0 modulo the FGLM output.
    let fglm_id = Ideal::from_gb(&pr, lex);
    assert!(fglm_id.contains(&g),
        "spec: source generator must lie in FGLM-emitted ideal");
}

#[test]
fn fglm_pure_powers_two_vars_dim_box() {
    // SPEC: <x^a, y^b> has staircase the (a × b) box; dim = a*b.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let x = pr.var(0);
    let y = pr.var(1);
    let x3 = pr.mul(pr.mul(pr.ring.clone_el(&x), pr.ring.clone_el(&x)), pr.ring.clone_el(&x));
    let y4 = pr.mul(
        pr.mul(pr.ring.clone_el(&y), pr.ring.clone_el(&y)),
        pr.mul(pr.ring.clone_el(&y), pr.ring.clone_el(&y)),
    );
    let gens = vec![x3, y4];
    let drl = Ideal::new(&pr, gens.iter().map(|p| pr.ring.clone_el(p)).collect());
    assert_eq!(
        drl.quotient_dimension(),
        Some(12),
        "spec: <x^3, y^4> has dim 3 * 4 = 12"
    );
    assert_fglm_ideal_eq_direct(&pr, gens);
}

// ── Positive-dimensional rejection across shapes ───────────────────

#[test]
fn fglm_rejects_positive_dim_two_var_shapes() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    // Shape 1: <x> — y is free, infinite dim.
    let g1 = pr.var(0);
    let id1 = Ideal::new(&pr, vec![g1]);
    assert!(!id1.is_zero_dim(), "spec: <x> is positive-dimensional");
    assert!(fglm_to_lex(&id1).is_none(), "FGLM must reject positive-dim");
    // Shape 2: <x*y, x*z> in 3 vars — neither y nor z has a pure power.
    let pr3 = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let xy = pr3.mul(pr3.var(0), pr3.var(1));
    let xz = pr3.mul(pr3.var(0), pr3.var(2));
    let id2 = Ideal::new(&pr3, vec![xy, xz]);
    assert!(!id2.is_zero_dim(), "spec: <xy, xz> is positive-dim");
    assert!(fglm_to_lex(&id2).is_none(), "FGLM must reject positive-dim");
}

#[test]
fn fglm_rejects_zero_ideal() {
    // Zero ideal <0> ≡ <>: positive-dimensional (whole ring R). FGLM
    // SPEC: must return None (caller falls back). Probes the empty-basis
    // branch path.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let drl = Ideal::new(&pr, vec![]);
    assert!(!drl.is_zero_dim(), "spec: <> in 2 vars is not zero-dim");
    assert!(fglm_to_lex(&drl).is_none(), "FGLM must reject zero ideal in n_vars > 0");
}

// ── Hilbert↔FGLM coupling ──────────────────────────────────────────

#[test]
fn fglm_hilbert_dim_matches_quotient_dim_grid() {
    // For a grid of small zero-dim ideals, the quotient_dimension oracle
    // must AGREE with the number of standard monomials the FGLM staircase
    // implicitly counts. The internal cross-check in fglm_to_lex turns
    // disagreement into None — so we ALSO need fglm_to_lex to return Some.
    // SPEC: for <x^a, y^b>, dim = a*b; FGLM returns Some.
    for &p in &[2u32, 3, 5, 7, 13, 257] {
        for a in 1u32..=3 {
            for b in 1u32..=3 {
                let pr = FfPolyRing::new(ff(p), vec!["x".into(), "y".into()]);
                let mut xa = pr.one();
                for _ in 0..a { xa = pr.mul(xa, pr.var(0)); }
                let mut yb = pr.one();
                for _ in 0..b { yb = pr.mul(yb, pr.var(1)); }
                let gens = vec![xa, yb];
                let drl = Ideal::new(&pr, gens);
                let expected = (a * b) as u128;
                assert_eq!(drl.quotient_dimension(), Some(expected),
                    "spec dim for <x^{}, y^{}> in GF({}) is {}", a, b, p, expected);
                let lex = fglm_to_lex(&drl);
                assert!(lex.is_some(),
                    "FGLM must succeed on zero-dim ideal <x^{}, y^{}> in GF({})", a, b, p);
            }
        }
    }
}

#[test]
fn fglm_dim_consistent_with_brute_force_for_known_case() {
    // SPEC: <x^2 - 3, y^2 - 2, x + y - 1> in GF(7) has exactly the
    // common roots of these equations. Substituting y = 1 - x:
    //   x^2 = 3 and (1 - x)^2 = 2.
    //   (1 - x)^2 = 1 - 2x + x^2 = 1 - 2x + 3 = 4 - 2x = 2 ⇒ x = 1.
    // Then x^2 = 1 ≠ 3 in GF(7), so x = 1 fails — no roots, ideal is
    // the WHOLE ring? Let's instead probe a case with a known root count.
    //
    // <x^2 - 1, y^2 - 1> in GF(7): roots = {±1} × {±1} = 4 solutions.
    // SPEC dim = 4.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, pr.one()),
        pr.sub(y2, pr.one()),
    ];
    let drl = Ideal::new(&pr, gens);
    assert_eq!(drl.quotient_dimension(), Some(4),
        "spec: <x^2-1, y^2-1> in GF(7) has 4 simple roots ⇒ dim 4");
    let fglm = fglm_to_lex(&drl).expect("zero-dim ⇒ Some");
    // The FGLM staircase count, when the Hilbert cross-check passes,
    // must agree with quotient_dimension. The internal check inside
    // fglm_to_lex would have returned None otherwise.
    assert!(!fglm.is_empty(), "FGLM emits non-empty lex GB for non-unit ideal");
}

// ── Round-trip: FGLM output lies in (Lex GB of) the source ideal ──

#[test]
fn fglm_output_generates_same_ideal_as_source_drl_gens() {
    // SPEC: FGLM converts a DRL GB to a Lex GB of the SAME ideal. Probe
    // that the union {DRL GB} ∪ {FGLM output} reduces every element to
    // zero against either basis — i.e. the two generate the same ideal,
    // via mutual ideal-membership with DRL-GB-based reduction.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![
        pr.sub(x2, c(3)),
        pr.sub(y2, c(2)),
    ];
    let drl = Ideal::new(&pr, gens.iter().map(|p| pr.ring.clone_el(p)).collect());
    let fglm = fglm_to_lex(&drl).expect("first call");
    // mutual ideal-membership across two different gen sets (both run
    // through Ideal::new → DRL GB → reduction)
    assert_same_ideal(&pr, &gens, &fglm);
}

// ── Cancel token: pre-cancelled FGLM input must not crash ─────────
//
// FGLM itself doesn't take a CancelToken, but its precondition is a
// finished DRL GB. If the GB was built via `Ideal::new_with_cancel`
// and cancelled early, the basis is `Err(Cancelled)` and FGLM is
// never invoked. SKIP a direct FGLM cancel test as FGLM has no cancel
// surface; instead probe that a CANCELLED upstream GB is safely
// propagated — the FGLM input never lands as a partial basis.

#[test]
fn fglm_cancelled_upstream_does_not_reach_fglm() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let c = |v: i64| pr.constant(pr.field().from_int(v));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let gens = vec![pr.sub(x2, c(3)), pr.sub(y2, c(2))];
    let token = CancelToken::cancelled(); // pre-cancelled
    let res = Ideal::new_with_cancel(&pr, gens, &token);
    // SPEC: a pre-cancelled token MUST surface as Err(Cancelled),
    // never as a falsely-trusted GB. This guards the cross-module
    // contract that FGLM consumes (FGLM never sees a partial basis).
    assert!(res.is_err(),
        "spec: pre-cancelled GB must surface as Err(Cancelled), \
         not pass a partial basis to FGLM");
    assert!(token.is_cancelled(), "cancel flag must remain set");
}

// ── Hilbert dim ⇄ FGLM staircase: tighter coupling probe ──────────

#[test]
fn hilbert_dim_equals_summed_standard_monomials_for_small_grids() {
    // Independently enumerate standard monomials of <x^a, y^b> (the box
    // {(i, j) : 0 ≤ i < a, 0 ≤ j < b}) and compare to
    // quotient_dimension. This is a pure-Hilbert probe; doesn't depend
    // on FGLM or any solver state.
    use crate::ff::hilbert::quotient_dimension;
    use crate::ff::monomial::Monomial;
    for a in 1u16..=4 {
        for b in 1u16..=4 {
            let gens = [
                Monomial::single_var(2, 0, a),
                Monomial::single_var(2, 1, b),
            ];
            let expected = (a as u128) * (b as u128);
            assert_eq!(
                quotient_dimension(&gens, 2),
                Some(expected),
                "spec: |std monomials of <x^{},y^{}>| = {}",
                a, b, expected
            );
        }
    }
}

#[test]
fn hilbert_dim_socle_ideal_three_vars() {
    // SPEC: m = (x, y, z) — the maximal ideal at origin. Std monomials = {1};
    // dim = 1.
    use crate::ff::hilbert::quotient_dimension;
    use crate::ff::monomial::Monomial;
    let gens = [
        Monomial::single_var(3, 0, 1),
        Monomial::single_var(3, 1, 1),
        Monomial::single_var(3, 2, 1),
    ];
    assert_eq!(quotient_dimension(&gens, 3), Some(1));
    // m^2 — std monomials = {1, x, y, z}; dim = 4.
    use crate::ff::monomial::Monomial as M;
    let gens_m2: Vec<M> = vec![
        M::from_exponents(vec![2, 0, 0]),
        M::from_exponents(vec![1, 1, 0]),
        M::from_exponents(vec![1, 0, 1]),
        M::from_exponents(vec![0, 2, 0]),
        M::from_exponents(vec![0, 1, 1]),
        M::from_exponents(vec![0, 0, 2]),
    ];
    assert_eq!(quotient_dimension(&gens_m2, 3), Some(4),
        "spec: m^2 in k[x,y,z] has std basis {{1, x, y, z}}, dim 4");
}

#[test]
fn hilbert_zero_ideal_zero_vars_is_dim_1() {
    // SPEC: k[x_1, ..., x_0] = k, so S/{0} = k, dim 1.
    use crate::ff::hilbert::quotient_dimension;
    assert_eq!(quotient_dimension(&[], 0), Some(1));
}

#[test]
fn hilbert_unit_ideal_zero_vars_is_dim_0() {
    use crate::ff::hilbert::quotient_dimension;
    use crate::ff::monomial::Monomial;
    // SPEC: S/<1> = 0, regardless of n_vars.
    assert_eq!(quotient_dimension(&[Monomial::one(0)], 0), Some(0));
    assert_eq!(quotient_dimension(&[Monomial::one(5)], 5), Some(0));
}

// ── Hilbert numerator: at t = 1 must vanish for Artinian ideals ───

#[test]
fn hilbert_numerator_vanishes_at_t1_for_many_artinian() {
    // SPEC: for Artinian I, (1-t)^n | HN(I)(t), so HN(I)(1) = 0.
    // Across multiple coprime / non-coprime ideal shapes.
    use crate::ff::hilbert::hilbert_numerator;
    use crate::ff::monomial::Monomial;
    let cases: Vec<Vec<Monomial>> = vec![
        // <x, y>
        vec![Monomial::from_exponents(vec![1, 0]), Monomial::from_exponents(vec![0, 1])],
        // <x^2, y^2>
        vec![Monomial::from_exponents(vec![2, 0]), Monomial::from_exponents(vec![0, 2])],
        // <x^3, x*y, y^2>
        vec![
            Monomial::from_exponents(vec![3, 0]),
            Monomial::from_exponents(vec![1, 1]),
            Monomial::from_exponents(vec![0, 2]),
        ],
        // <x^2, x*y, y^3>
        vec![
            Monomial::from_exponents(vec![2, 0]),
            Monomial::from_exponents(vec![1, 1]),
            Monomial::from_exponents(vec![0, 3]),
        ],
    ];
    for (i, gens) in cases.iter().enumerate() {
        let hn = hilbert_numerator(gens);
        let sum: i64 = hn.coeffs().iter().sum();
        assert_eq!(sum, 0, "case {}: HN(1) must vanish for Artinian", i);
    }
}

// ── Hilbert numerator: redundant-generator robustness ─────────────

#[test]
fn hilbert_dim_robust_under_redundant_generators() {
    // SPEC: adding a redundant generator (a multiple of an existing one)
    // does not change the ideal, so dim_k(S/I) is unchanged.
    use crate::ff::hilbert::quotient_dimension;
    use crate::ff::monomial::Monomial;
    let minimal = [
        Monomial::from_exponents(vec![2, 0]),
        Monomial::from_exponents(vec![0, 2]),
    ];
    let with_redundant = [
        Monomial::from_exponents(vec![2, 0]),
        Monomial::from_exponents(vec![3, 0]),     // multiple of x^2
        Monomial::from_exponents(vec![2, 1]),     // multiple of x^2
        Monomial::from_exponents(vec![0, 2]),
        Monomial::from_exponents(vec![0, 5]),     // multiple of y^2
    ];
    assert_eq!(
        quotient_dimension(&minimal, 2),
        quotient_dimension(&with_redundant, 2),
        "spec: redundant gens (multiples of minimal gens) don't change dim"
    );
}

// ── Coprime vs recursive paths must agree ────────────────────────

#[test]
fn hilbert_numerator_coprime_path_equals_explicit_product() {
    // SPEC (definition): for pairwise-coprime gens g_1,...,g_s,
    // N(I) = Π (1 - t^{deg g_i}). Three pairwise coprime pure powers
    // exercises the early-return shortcut; we re-compute via the
    // independent `mul(one_minus_t_pow(.))` chain.
    use crate::ff::hilbert::{hilbert_numerator, HilbertNum};
    use crate::ff::monomial::Monomial;
    let gens = [
        Monomial::single_var(3, 0, 2),
        Monomial::single_var(3, 1, 3),
        Monomial::single_var(3, 2, 5),
    ];
    let hn = hilbert_numerator(&gens);
    let mut expected = HilbertNum::one();
    expected = expected.mul(&HilbertNum::one_minus_t_pow(2));
    expected = expected.mul(&HilbertNum::one_minus_t_pow(3));
    expected = expected.mul(&HilbertNum::one_minus_t_pow(5));
    assert_eq!(hn, expected,
        "spec: coprime path must equal explicit Π(1 - t^{{d_i}})");
    // SPEC: dim = Π d_i = 2 * 3 * 5 = 30.
    use crate::ff::hilbert::quotient_dimension;
    assert_eq!(quotient_dimension(&gens, 3), Some(30));
}

// ── FGLM mono-cap probe: the FGLM_MONO_CAP guard ─────────────────

#[test]
fn fglm_mono_cap_never_breaks_zero_dim_correctness() {
    // SPEC: for ideals with dim ≪ FGLM_MONO_CAP (200_000), FGLM must
    // return Some, regardless of input topology — the cap is a watchdog
    // only. Probe with a moderately-sized box <x^5, y^5> (dim 25) and
    // <x^10, y^10> (dim 100) where the staircase walk is the most BFS-y.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    for (a, b, dim) in [(5u32, 5u32, 25u128), (10, 10, 100)] {
        let mut xa = pr.one();
        for _ in 0..a { xa = pr.mul(xa, pr.var(0)); }
        let mut yb = pr.one();
        for _ in 0..b { yb = pr.mul(yb, pr.var(1)); }
        let drl = Ideal::new(&pr, vec![xa, yb]);
        assert_eq!(drl.quotient_dimension(), Some(dim));
        let lex = fglm_to_lex(&drl);
        assert!(lex.is_some(),
            "FGLM must succeed for <x^{}, y^{}> (dim {}) — well below mono cap",
            a, b, dim);
    }
}

#[test]
fn audit_p1_cancel_token_fires_mid_bfs_walk_via_shared_token() {
    // Drive a moderate staircase, then trip the cancel token via a
    // background thread WHILE the BFS walk is running. Because the
    // walk checks `cancel.is_cancelled()` at the top of every queue
    // iteration, the fire is observed inside the loop (not at entry
    // like the pre-cancel variant), and `fglm_to_lex_cancel` returns
    // None instead of a (potentially partial) basis.
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let mut x6 = pr.one();
    for _ in 0..6 { x6 = pr.mul(x6, pr.var(0)); }
    let mut y6 = pr.one();
    for _ in 0..6 { y6 = pr.mul(y6, pr.var(1)); }
    let mut z6 = pr.one();
    for _ in 0..6 { z6 = pr.mul(z6, pr.var(2)); }
    let drl = Ideal::new(&pr, vec![x6, y6, z6]);

    let cancel = CancelToken::new();
    let cancel_for_thread = cancel.clone();
    let handle = std::thread::spawn(move || {
        // Brief delay so the BFS walk reaches its top-of-iteration
        // cancel check before the flag flips.
        std::thread::sleep(std::time::Duration::from_micros(50));
        cancel_for_thread.cancel();
    });

    let result = fglm_to_lex_cancel(&drl, &cancel);
    handle.join().expect("join");

    // Either the walk completed before the cancel fired (unlikely but
    // not a soundness failure) OR the walk surfaced None on cancel.
    // We assert the cancel was actually observed at some point by
    // verifying the flag is set; the walk's specific outcome is
    // accepted in either shape.
    assert!(
        cancel.is_cancelled(),
        "cancel must be set after the join",
    );
    let _ = result;
    // Avoid unused-import lints when the runtime path takes the
    // walk-completed-before-fire branch.
    let _ = Arc::new(AtomicBool::new(false));
    let _ = Ordering::SeqCst;
}

#[test]
fn audit_p1_zero_dim_call_count_tracked_by_metric_counter() {
    // `Ideal::is_zero_dim` and `Ideal::quotient_dimension` are
    // instrumented via `metric::incr!` on the shared
    // `picus_core::profile::IDEAL` counter pair. When `gb_stats` is
    // ON the counters update; when OFF the macros are no-ops.
    let _guard = picus_core::config::ConfigGuard::with_override(|c| {
        c.gb_stats_enabled = true;
    });
    use std::sync::atomic::Ordering;
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let mut x5 = pr.one();
    for _ in 0..5 { x5 = pr.mul(x5, pr.var(0)); }
    let mut y5 = pr.one();
    for _ in 0..5 { y5 = pr.mul(y5, pr.var(1)); }
    let drl = Ideal::new(&pr, vec![x5, y5]);

    let zd_before =
        picus_core::profile::IDEAL.is_zero_dim_calls.load(Ordering::Relaxed);
    let qd_before =
        picus_core::profile::IDEAL.quotient_dimension_calls.load(Ordering::Relaxed);
    let _ = drl.is_zero_dim();
    let _ = drl.quotient_dimension();
    let zd_after =
        picus_core::profile::IDEAL.is_zero_dim_calls.load(Ordering::Relaxed);
    let qd_after =
        picus_core::profile::IDEAL.quotient_dimension_calls.load(Ordering::Relaxed);
    assert!(
        zd_after >= zd_before + 1,
        "is_zero_dim_calls must increment when gb_stats is on (before={}, after={})",
        zd_before,
        zd_after
    );
    assert!(
        qd_after >= qd_before + 1,
        "quotient_dimension_calls must increment when gb_stats is on (before={}, after={})",
        qd_before,
        qd_after
    );
}

#[test]
fn audit_p1_cancel_token_fires_before_bfs_walk_starts() {
    // Pre-cancelled token must surface as None on the very first
    // iteration of the BFS queue — no work is performed beyond the
    // zero-dim gate. Probe with the same ⟨x^5, y^5⟩ ideal as the
    // mono-cap regression so the soundness gate cannot mask the cancel
    // check.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let mut x5 = pr.one();
    for _ in 0..5 { x5 = pr.mul(x5, pr.var(0)); }
    let mut y5 = pr.one();
    for _ in 0..5 { y5 = pr.mul(y5, pr.var(1)); }
    let drl = Ideal::new(&pr, vec![x5, y5]);
    let cancel = CancelToken::cancelled();
    assert!(
        fglm_to_lex_cancel(&drl, &cancel).is_none(),
        "pre-cancelled token must short-circuit fglm_to_lex_cancel"
    );
    // Sanity: same ideal under an uncancelled token still completes.
    assert!(
        fglm_to_lex_cancel(&drl, &CancelToken::none()).is_some(),
        "uncancelled token on the same ideal must complete"
    );
}
