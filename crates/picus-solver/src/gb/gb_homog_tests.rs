use super::*;
use crate::ff::field::PrimeField;
use crate::ff::monomial::MonomialOrder;
use crate::gb::ideal::compute_gb_with_order;
use crate::poly::FfPolyRing;
use num_bigint::BigUint;
use std::collections::BTreeSet;

/// Compare two GBs by their *leading-monomial sets* in DegRevLex on `P`.
/// This is the standard equivalence check: two reduced,
/// monic, DegRevLex GBs of the same ideal must have identical LM sets.
fn lm_set(pr: &FfPolyRing, gb: &[Poly]) -> BTreeSet<Vec<usize>> {
    let ctx = pr.ctx();
    let n = pr.n_vars();
    let mut s = BTreeSet::new();
    for p in gb {
        if let Some(m) = p.leading_monomial(ctx) {
            let exps: Vec<usize> = (0..n).map(|i| m.exponent(i) as usize).collect();
            s.insert(exps);
        }
    }
    s
}

fn pr_xy(p: u32) -> FfPolyRing {
    let field = PrimeField::new(BigUint::from(p));
    FfPolyRing::new(field, vec!["x".into(), "y".into()])
}

fn pr_xyz(p: u32) -> FfPolyRing {
    let field = PrimeField::new(BigUint::from(p));
    FfPolyRing::new(field, vec!["x".into(), "y".into(), "z".into()])
}

#[test]
fn test_homog_empty() {
    let pr = pr_xy(17);
    let gb = compute_gb_by_homog(&pr, vec![], &CancelToken::none());
    assert!(gb.is_empty());
}

#[test]
fn test_homog_single_homog_input() {
    // f = x + y already deg-1 homog → both drivers should give {x+y}
    // up to monic normalization.
    let pr = pr_xy(17);
    let f = pr.add(pr.var(0), pr.var(1));
    let gb_direct = compute_gb_with_order(
        &pr,
        vec![pr.clone_poly(&f)],
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_homog = compute_gb_by_homog(&pr, vec![f], &CancelToken::none());
    assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog));
}

#[test]
fn test_homog_bitcube_pair() {
    // x^2 - x  and  y^2 - y   (the bit-prop pair).  GB = those + x*y - ?
    // Just check LM-set equivalence with direct.
    let pr = pr_xy(17);
    let x = pr.var(0);
    let y = pr.var(1);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
    let f1 = pr.sub(xx, pr.clone_poly(&x));
    let f2 = pr.sub(yy, pr.clone_poly(&y));
    let gb_direct = compute_gb_with_order(
        &pr,
        vec![pr.clone_poly(&f1), pr.clone_poly(&f2)],
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_homog = compute_gb_by_homog(&pr, vec![f1, f2], &CancelToken::none());
    assert_eq!(
        lm_set(&pr, &gb_direct),
        lm_set(&pr, &gb_homog),
        "bit-cube pair: direct LMs vs homog LMs"
    );
}

#[test]
fn test_homog_bitcube_plus_bitsum() {
    // The classic bit-decomp shape: bit cubes + bitsum.
    // x^2 - x, y^2 - y, x + 2y - 3   (so x = 1, y = 1 is the only soln in F17).
    let pr = pr_xy(17);
    let x = pr.var(0);
    let y = pr.var(1);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
    let bc1 = pr.sub(xx, pr.clone_poly(&x));
    let bc2 = pr.sub(yy, pr.clone_poly(&y));
    // x + 2y - 3
    let two = pr.constant(pr.field().from_int(2));
    let three = pr.constant(pr.field().from_int(3));
    let two_y = pr.mul(two, pr.clone_poly(&y));
    let bs = pr.sub(pr.add(pr.clone_poly(&x), two_y), three);
    let gens = vec![bc1, bc2, bs];
    let gb_direct = compute_gb_with_order(
        &pr,
        gens.iter().map(|p| pr.clone_poly(p)).collect(),
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
    assert_eq!(
        lm_set(&pr, &gb_direct),
        lm_set(&pr, &gb_homog),
        "bit-cube + bitsum: direct LMs vs homog LMs"
    );
}

#[test]
fn test_homog_rabinowitsch() {
    // 1 - y * f trick: f = x^2 + 1, augment with `1 - z*(x^2+1)`.
    // Just check equivalence with direct on  {x^2 + 1, 1 - z*(x^2+1)}.
    let pr = pr_xyz(17);
    let x = pr.var(0);
    let z = pr.var(2);
    let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
    let one = pr.one();
    let f = pr.add(xx, pr.clone_poly(&one));
    let zf = pr.mul(pr.clone_poly(&z), pr.clone_poly(&f));
    let rab = pr.sub(one, zf);
    let gens = vec![f, rab];
    let gb_direct = compute_gb_with_order(
        &pr,
        gens.iter().map(|p| pr.clone_poly(p)).collect(),
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
    assert_eq!(
        lm_set(&pr, &gb_direct),
        lm_set(&pr, &gb_homog),
        "Rabinowitsch: direct LMs vs homog LMs"
    );
}

#[test]
fn test_homog_chunked_add_small() {
    // Chunked-add shape (the killer benchmark family):
    //   a + b - 2*c - r = 0   (r = chunk in {0..3}, c = carry in {0..1})
    //   a^2 - a, b^2 - b, c^2 - c   (bit cubes)
    // Equivalence check on this 5-poly system.
    let p: u32 = 65521; // a small-ish prime, big enough so 4 has an inverse
    let field = PrimeField::new(BigUint::from(p));
    let pr = FfPolyRing::new(field, vec!["a".into(), "b".into(), "c".into(), "r".into()]);
    let a = pr.var(0);
    let b = pr.var(1);
    let c = pr.var(2);
    let r = pr.var(3);
    let aa = pr.mul(pr.clone_poly(&a), pr.clone_poly(&a));
    let bb = pr.mul(pr.clone_poly(&b), pr.clone_poly(&b));
    let cc = pr.mul(pr.clone_poly(&c), pr.clone_poly(&c));
    let bc_a = pr.sub(aa, pr.clone_poly(&a));
    let bc_b = pr.sub(bb, pr.clone_poly(&b));
    let bc_c = pr.sub(cc, pr.clone_poly(&c));
    let two = pr.constant(pr.field().from_int(2));
    let two_c = pr.mul(two, pr.clone_poly(&c));
    // a + b - 2c - r
    let chunk = pr.sub(
        pr.sub(pr.add(pr.clone_poly(&a), pr.clone_poly(&b)), two_c),
        pr.clone_poly(&r),
    );
    let gens = vec![bc_a, bc_b, bc_c, chunk];
    let gb_direct = compute_gb_with_order(
        &pr,
        gens.iter().map(|p| pr.clone_poly(p)).collect(),
        &CancelToken::none(),
        MonomialOrder::DegRevLex,
    );
    let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
    assert_eq!(
        lm_set(&pr, &gb_direct),
        lm_set(&pr, &gb_homog),
        "chunked-add: direct LMs vs homog LMs"
    );
}

/// Full reduced-GB differential oracle for `compute_gb_by_homog` (the
/// engine's `ByHomog` strategy) against the per-pair direct driver, over
/// random low-degree generator sets. The LM-set checks above are
/// necessary but not sufficient for ideal equality; the reduced GB under
/// a fixed order is unique, so comparing the full reduced, monic bases
/// term-for-term is the oracle that would catch a by-homog soundness
/// divergence (homogenise/dehomogenise losing or adding a solution).
/// `compute_gb_direct` is the reference — config-independent per-pair
/// Buchberger, the same raw entry by-homog uses internally — so the test
/// can't accidentally compare ByHomog against itself.
#[test]
fn homog_reduced_gb_matches_direct_random() {
    use crate::gb::ideal::{compute_gb_direct, interreduce_basis};

    const GV: usize = 3;
    const P: u64 = 101;
    let field = PrimeField::new(BigUint::from(P as u32));
    let pr = FfPolyRing::new(field, (0..GV).map(|i| format!("v{i}")).collect());

    // Self-contained deterministic LCG (no test-only RNG dependency).
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state >> 33
    };

    // Canonical form of a reduced, monic GB (interreduce_basis already
    // monic-normalises): each poly's index-keyed terms, bases sorted, for
    // an order-independent set comparison.
    let canon = |gb: Vec<Poly>| -> Vec<Vec<(BigUint, Vec<(usize, u16)>)>> {
        let reduced = interreduce_basis(&pr, gb, &CancelToken::none());
        let ctx = pr.ctx();
        let mut out: Vec<_> = reduced.iter().map(|p| p.collect_terms_idx(ctx)).collect();
        out.sort();
        out
    };

    for _ in 0..300 {
        let n_gen = 2 + (next() % 3) as usize; // 2–4 generators
        let mut gens: Vec<Poly> = Vec::new();
        for _ in 0..n_gen {
            let n_term = 1 + (next() % 3) as usize; // 1–3 terms
            let mut poly = pr.zero();
            for _ in 0..n_term {
                let coeff = pr.constant(pr.field().from_u64(1 + next() % (P - 1)));
                let mut term = coeff;
                for v in 0..GV {
                    if next() % 2 == 1 {
                        term = pr.mul(term, pr.var(v));
                    }
                }
                poly = pr.add(poly, term);
            }
            if !pr.is_zero(&poly) {
                gens.push(poly);
            }
        }
        if gens.is_empty() {
            continue;
        }

        let gb_direct = compute_gb_direct(
            &pr,
            gens.iter().map(|p| pr.clone_poly(p)).collect(),
            &CancelToken::none(),
            MonomialOrder::DegRevLex,
        );
        let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());

        assert_eq!(
            canon(gb_direct),
            canon(gb_homog),
            "by-homog reduced GB diverges from direct per-pair",
        );
    }
}
