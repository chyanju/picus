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
