use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;

fn ff(p: u32) -> PrimeField {
    PrimeField::new(BigUint::from(p))
}

/// Multiset of leading monomials (as exponent vectors) of `basis`.
fn lm_multiset(pr: &FfPolyRing, basis: &[Poly]) -> Vec<Vec<u16>> {
    let ctx = pr.ctx();
    let n = pr.n_vars();
    let mut v: Vec<Vec<u16>> = basis
        .iter()
        .filter_map(|p| p.leading_monomial(ctx))
        .map(|m| (0..n).map(|i| m.exponent(i)).collect())
        .collect();
    v.sort();
    v
}

#[test]
fn interreduce_dedups_equal_leading_monomials() {
    // A non-minimal Gröbner basis of I = (x²-1, y²-1) over GF(17):
    // append x²+y²-2 ∈ I, whose leading monomial x² equals the first
    // generator's. `interreduce_basis` must collapse to the canonical
    // reduced GB {x²-1, y²-1} — no duplicate leading monomial survives.
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let one = pr.constant(pr.field().from_int(1));
    let two = pr.constant(pr.field().from_int(2));
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let g1 = pr.sub(pr.clone_poly(&x2), pr.clone_poly(&one)); // x² - 1
    let g2 = pr.sub(pr.clone_poly(&y2), pr.clone_poly(&one)); // y² - 1
    // x² + y² - 2  (redundant; LT = x²)
    let g3 = pr.sub(pr.add(x2, y2), two);

    // Canonical reduced GB from the two real generators.
    let reduced = compute_gb_with_order(
        &pr,
        vec![pr.clone_poly(&g1), pr.clone_poly(&g2)],
        &CancelToken::none(),
        FfOrder::DegRevLex,
    );

    let non_minimal = vec![g1, g2, g3];
    let out = interreduce_basis(&pr, non_minimal, &CancelToken::none());

    // Same leading-monomial set, same cardinality (minimal), and no
    // duplicate leading monomial.
    assert_eq!(lm_multiset(&pr, &out), lm_multiset(&pr, &reduced));
    assert_eq!(out.len(), reduced.len(), "result must be minimal");
    let lms = lm_multiset(&pr, &out);
    let mut uniq = lms.clone();
    uniq.dedup();
    assert_eq!(lms.len(), uniq.len(), "no duplicate leading monomial: {:?}", lms);
}

#[test]
fn test_contains_simple() {
    // I = (x - 3) over GF(17). Then (x^2 - 9) ∈ I, but x ∉ I.
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let three = pr.field().from_int(3);
    let nine = pr.field().from_int(9);
    let p1 = pr.sub(pr.var(0), pr.constant(three));
    let ideal = Ideal::new(&pr, vec![p1]);

    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let x2_minus_9 = pr.sub(x2, pr.constant(nine));
    assert!(ideal.contains(&x2_minus_9));
    assert!(!ideal.contains(&x));
}

#[test]
fn test_whole_ring() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let one = pr.one();
    let ideal = Ideal::new(&pr, vec![one]);
    assert!(ideal.is_whole_ring());
    assert!(ideal.is_zero_dim());
}

#[test]
fn test_is_zero_dim_yes() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let one = pr.field().from_int(1);
    let two = pr.field().from_int(2);
    let p1 = pr.sub(pr.var(0), pr.constant(one));
    let p2 = pr.sub(pr.var(1), pr.constant(two));
    let ideal = Ideal::new(&pr, vec![p1, p2]);
    assert!(ideal.is_zero_dim());
}

#[test]
fn test_is_zero_dim_no() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into()]);
    let xy = pr.mul(pr.var(0), pr.var(1));
    let ideal = Ideal::new(&pr, vec![xy]);
    assert!(!ideal.is_zero_dim());
}

#[test]
fn test_min_poly_constant_var() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let five = pr.field().from_int(5);
    let p1 = pr.sub(pr.var(0), pr.constant(five));
    let ideal = Ideal::new(&pr, vec![p1]);
    let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
    assert_eq!(mp.len(), 2);
    let fp = &pr.field();
    let neg_five = fp.neg(&pr.field().from_int(5));
    assert!(fp.eq_el(&mp[0], &neg_five));
    assert!(fp.is_one(&mp[1]));
}

#[test]
fn test_min_poly_quadratic() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let x = pr.var(0);
    let x2 = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let one = pr.one();
    let p = pr.sub(x2, one);
    let ideal = Ideal::new(&pr, vec![p]);
    let mp = ideal.min_poly(0).expect("zero-dim, should have minpoly");
    assert_eq!(mp.len(), 3);
    let fp = &pr.field();
    let neg_one = fp.neg(&fp.one());
    assert!(fp.eq_el(&mp[0], &neg_one));
    assert!(fp.is_zero(&mp[1]));
    assert!(fp.is_one(&mp[2]));
}

#[test]
fn test_normalize() {
    let pr = FfPolyRing::new(ff(17), vec!["x".into()]);
    let three = pr.field().from_int(3);
    let six = pr.field().from_int(6);
    let term1 = pr.scale(three, pr.var(0));
    let p = pr.add(term1, pr.constant(six));
    let ideal = Ideal::new(&pr, vec![]);
    let normalized = ideal.normalize(&p);
    let lc = leading_coefficient(&pr.ring, &normalized, FfOrder::DegRevLex);
    assert!(pr.field().is_one(&lc));
}

// ────────── extend_with_cancel: empty-after-filter early return (lines 92-93) ──────────

#[test]
fn extend_with_cancel_zero_new_poly_is_noop() {
    // A non-empty ideal extended by only a zero polynomial is unchanged:
    // the zero filter empties new_polys and the early return hands `self`
    // back with the same basis.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let p1 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(1)));
    let ideal = Ideal::new(&pr, vec![p1]);
    let before = ideal.basis.len();
    assert!(before > 0, "precondition: non-empty basis");
    let extended = ideal
        .extend_with_cancel(vec![pr.zero()], &CancelToken::none())
        .expect("no-op extend cannot cancel/fail");
    assert_eq!(extended.basis.len(), before, "basis unchanged by zero extend");
    // x is still in the ideal, z-like extension added nothing new: x-1 ∈ I.
    let x_m1 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(1)));
    assert!(extended.contains(&x_m1));
}

// ────────── extend_with_cancel_traced: empty-after-filter early return (line 145) ──────────

#[test]
fn extend_with_cancel_traced_zero_new_poly_is_noop() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let p1 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(1)));
    let ideal = Ideal::new(&pr, vec![p1]);
    let before = ideal.basis.len();
    let mut tracer = crate::gb::tracer::GbTracer::new(4);
    let extended = ideal
        .extend_with_cancel_traced(vec![pr.zero()], &CancelToken::none(), &mut tracer)
        .expect("no-op traced extend cannot cancel/fail");
    assert_eq!(extended.basis.len(), before, "basis unchanged");
    // Early return happens before any Buchberger step, so the tracer
    // observed nothing.
    assert_eq!(tracer.basis_count(), 0, "tracer not fed on the no-op path");
}

// ────────── quotient_dimension special cases (lines 233, 250, 253, 260) ──────────

#[test]
fn quotient_dimension_whole_ring_is_zero() {
    // 1 ∈ I ⇒ R/I = 0, dimension 0.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let ideal = Ideal::new(&pr, vec![pr.one()]);
    assert!(ideal.is_whole_ring());
    assert_eq!(ideal.quotient_dimension(), Some(0));
}

#[test]
fn quotient_dimension_empty_ideal_is_none() {
    // The zero ideal: R/I = R is infinite-dimensional ⇒ None.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let ideal = Ideal::new(&pr, vec![]);
    assert!(ideal.basis.is_empty());
    assert_eq!(ideal.quotient_dimension(), None);
}

#[test]
fn quotient_dimension_skips_zero_polys() {
    // A hand-built (zero-padded) basis {x-1, 0, y-2}: leading monomials
    // x and y cover both variables ⇒ zero-dimensional with a single
    // standard monomial {1} ⇒ dim 1. The interior zero poly must be
    // skipped during leading-monomial extraction.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let x_m1 = pr.sub(pr.var(0), pr.constant(pr.field().from_int(1)));
    let y_m2 = pr.sub(pr.var(1), pr.constant(pr.field().from_int(2)));
    let ideal = Ideal::from_gb(&pr, vec![x_m1, pr.zero(), y_m2]);
    assert!(!ideal.is_whole_ring());
    assert_eq!(ideal.quotient_dimension(), Some(1));
}

// ────────── leading_monomial / leading_coefficient helpers (lines 381-387, 397) ──────────

#[test]
fn leading_monomial_of_quadratic() {
    // x^2 + 1 in DegRevLex: leading monomial is x^2 = exponent vector [2,0].
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
    let xx = pr.mul(pr.var(0), pr.var(0));
    let p = pr.add(xx, pr.one());
    let lm = leading_monomial(&pr.ring, &p, FfOrder::DegRevLex).expect("nonzero poly has lm");
    assert_eq!(lm.exponent(0), 2);
    assert_eq!(lm.exponent(1), 0);
}

#[test]
fn leading_monomial_of_zero_is_none() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let z = pr.zero();
    assert!(leading_monomial(&pr.ring, &z, FfOrder::DegRevLex).is_none());
}

#[test]
fn leading_coefficient_of_quadratic() {
    // 3*x^2 + 2 over GF(7): leading coefficient is 3.
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let xx = pr.mul(pr.var(0), pr.var(0));
    let three_x2 = pr.scale(pr.field().from_int(3), xx);
    let p = pr.add(three_x2, pr.constant(pr.field().from_int(2)));
    let lc = leading_coefficient(&pr.ring, &p, FfOrder::DegRevLex);
    assert!(pr.field().eq_el(&lc, &pr.field().from_int(3)));
}

#[test]
fn leading_coefficient_of_zero_is_zero() {
    let pr = FfPolyRing::new(ff(7), vec!["x".into()]);
    let z = pr.zero();
    let lc = leading_coefficient(&pr.ring, &z, FfOrder::DegRevLex);
    assert!(pr.field().is_zero(&lc));
}

#[test]
fn is_zero_dim_yes_with_univariate_power_leading_terms() {
    // GF(7), three vars. <x^2 - 1, y^2 - 1, z^2 - 1>: each generator is
    // univariate of degree 2 and is already a reduced Gröbner basis, so
    // the leading monomials are the pure powers x^2, y^2, z^2. Each pins
    // exactly one variable (`multiple = false`), so `covered` grows to
    // {0,1,2} = n_vars and the final `covered.len() == n_vars` evaluates
    // to true. Complements the linear-pin fixture by driving the same
    // return through degree-2 pure-power leading terms.
    let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into(), "z".into()]);
    let one = pr.one();
    let x2 = pr.mul(pr.var(0), pr.var(0));
    let y2 = pr.mul(pr.var(1), pr.var(1));
    let z2 = pr.mul(pr.var(2), pr.var(2));
    let gens = vec![
        pr.sub(x2, pr.clone_poly(&one)),
        pr.sub(y2, pr.clone_poly(&one)),
        pr.sub(z2, one),
    ];
    let ideal = Ideal::new(&pr, gens);
    assert!(!ideal.is_whole_ring());
    assert!(
        ideal.is_zero_dim(),
        "three univariate quadratics cover all three variables ⇒ zero-dimensional"
    );
    // Cross-check against the Hilbert oracle: dim_k(R/I) = 2*2*2 = 8.
    assert_eq!(ideal.quotient_dimension(), Some(8));
}

#[test]
fn is_zero_dim_no_with_mixed_single_and_multi_var_leading_terms() {
    // GF(17), three vars. <x - 1, y*z>: the GB has a single-var leading
    // term (x, covers var 0) and a two-variable leading term (y*z), which
    // drives the `multiple = true; break` path in `is_zero_dim`. Neither
    // y nor z gets a pure-power leading term, so `covered` (= {0}) is a
    // strict subset of {0,1,2} → not zero-dimensional.
    let pr = FfPolyRing::new(ff(17), vec!["x".into(), "y".into(), "z".into()]);
    let x_m1 = pr.sub(pr.var(0), pr.one());
    let yz = pr.mul(pr.var(1), pr.var(2));
    let ideal = Ideal::new(&pr, vec![x_m1, yz]);
    assert!(
        !ideal.is_zero_dim(),
        "y*z leaves y,z uncovered ⇒ positive-dimensional"
    );
}
