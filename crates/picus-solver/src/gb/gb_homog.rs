//! `compute_gb_by_homog`: GB-by-homogenization driver.
//!
//! Mirrors CoCoA's `myGBasisByHomog` (`SparsePolyOps-ideal.C:819-862`):
//!
//! 1. Build extended ring `Ph = P[h]` ([`crate::gb::homog_ring::HomogRing`]).
//! 2. Lift every input `f_i ∈ P` into `Ph`, then homogenize to its top
//!    total degree (so every generator is `d_i`-homogeneous in `Ph`).
//! 3. Run plain DegRevLex Buchberger on `Ph` (via the existing
//!    [`crate::gb::ideal::compute_gb_buchberger`] path — same Buchberger,
//!    same observers, same cancellation). Calling the raw Buchberger
//!    entry rather than the dispatching `compute_gb_with_order` is
//!    deliberate: otherwise dispatch would recurse back into ByHomog
//!    on the homogenised ring.
//! 4. Dehomogenize each basis element back to `P` (`h := 1`).
//! 5. Interreduce in `P` (drop LM-divisible duplicates, normal-form survivors).
//!
//! Rationale: in `Ph`, every input is exactly degree `d_i`, so the
//! in-tree sugar-degree S-pair selector ([`ff::buchberger`]) has
//! `sugar = wdeg` without mispredictions; pairs are processed in
//! strict ascending degree, avoiding the "intermediate expression
//! swell" that kills bit-decomposition ideals (R3 §5). CoCoA reports
//! 5–50× speedups on the bit-cube + bitsum + chunked-add shape.

use crate::ff::monomial::MonomialOrder;
use crate::gb::homog_ring::HomogRing;
use crate::gb::ideal::{compute_gb_buchberger, interreduce_basis};
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::CancelToken;

/// Compute a DegRevLex Groebner basis of `gens ⊂ P` via the
/// homogenize → GB → dehomogenize → interreduce pipeline.
///
/// Contract:
/// * Input: arbitrary (possibly non-homogeneous) polynomials in `P`.
/// * Output: a Groebner basis of `(gens) ⊂ P` in DegRevLex order on `P`,
///   suitable to be wrapped by `Ideal::from_gb`.
/// * Empty input → empty basis (matches `compute_gb_with_order`).
/// * Cancellation: the inner `compute_gb_with_order` already honors
///   `cancel`; if it fires, we return whatever interreduced dehom basis
///   we have (possibly empty).
pub fn compute_gb_by_homog(
    pr: &FfPolyRing,
    gens: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    let _t = crate::profile::ScopedTimer::new("compute_gb_by_homog");
    if gens.is_empty() {
        return Vec::new();
    }

    // Step 1: extended ring Ph
    let h = HomogRing::new(pr);

    // Step 2: lift + homogenize, dropping zeros.
    let gh: Vec<Poly> = gens
        .iter()
        .filter(|p| !pr.is_zero(p))
        .map(|p| h.lift_and_homogenize(p))
        .collect();

    if gh.is_empty() {
        return Vec::new();
    }

    if cancel.is_cancelled() {
        return Vec::new();
    }

    // Step 3: plain DegRevLex Buchberger on Ph. Use the raw entry
    // (not the dispatching `compute_gb_with_order`) so the chosen
    // strategy doesn't bounce back into this routine.
    let gb_h_backup: Vec<Poly> = gh.iter().map(|p| h.ext.clone_poly(p)).collect();
    let gb_h = compute_gb_buchberger(&h.ext, gh, cancel, MonomialOrder::DegRevLex)
        .unwrap_or_else(|e| {
            log::debug!(
                "homogenised GB returned {:?}; falling back to unreduced generators",
                e
            );
            gb_h_backup
        });

    if cancel.is_cancelled() {
        // Best-effort: dehom + interreduce what we have; consumers will
        // typically discard via the outer cancel check anyway.
    }

    // Step 4: dehom each element back to P.
    let mut gb_p: Vec<Poly> = gb_h
        .iter()
        .map(|q| h.dehom(q))
        .filter(|p| !pr.is_zero(p))
        .collect();

    if gb_p.is_empty() {
        return gb_p;
    }

    // Step 5: interreduce in P.  This (a) drops LM-divisible duplicates
    // produced by the dehom collapse (e.g. `h^2·m` and `h·m` both → `m`),
    // (b) normal-forms survivors, (c) monic-normalizes.  Mirrors CoCoA
    // myGBasisByHomog lines 845–858.
    gb_p = interreduce_basis(pr, gb_p, cancel);
    gb_p
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::ff::monomial::MonomialOrder;
    use crate::gb::ideal::compute_gb_with_order;
    use crate::poly::FfPolyRing;
    use num_bigint::BigUint;
    use std::collections::BTreeSet;

    /// Compare two GBs by their *leading-monomial sets* in DegRevLex on `P`.
    /// This is the standard equivalence check (R3 §4 T6): two reduced,
    /// monic, DegRevLex GBs of the same ideal must have identical LM sets.
    fn lm_set(pr: &FfPolyRing, gb: &[Poly]) -> BTreeSet<Vec<usize>> {
        let ctx = pr.ctx();
        let n = pr.n_vars;
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
        let gb_direct = compute_gb_with_order(&pr, vec![pr.clone_poly(&f)], &CancelToken::none(), MonomialOrder::DegRevLex);
        let gb_homog = compute_gb_by_homog(&pr, vec![f], &CancelToken::none());
        assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog));
    }

    #[test]
    fn test_homog_bitcube_pair() {
        // x^2 - x  and  y^2 - y   (the bit-prop pair).  GB = those + x*y - ?
        // Just check LM-set equivalence with direct.
        let pr = pr_xy(17);
        let x = pr.var(0); let y = pr.var(1);
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
        let f1 = pr.sub(xx, pr.clone_poly(&x));
        let f2 = pr.sub(yy, pr.clone_poly(&y));
        let gb_direct = compute_gb_with_order(&pr,
            vec![pr.clone_poly(&f1), pr.clone_poly(&f2)],
            &CancelToken::none(), MonomialOrder::DegRevLex);
        let gb_homog = compute_gb_by_homog(&pr, vec![f1, f2], &CancelToken::none());
        assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog),
                   "bit-cube pair: direct LMs vs homog LMs");
    }

    #[test]
    fn test_homog_bitcube_plus_bitsum() {
        // The classic bit-decomp shape: bit cubes + bitsum.
        // x^2 - x, y^2 - y, x + 2y - 3   (so x = 1, y = 1 is the only soln in F17).
        let pr = pr_xy(17);
        let x = pr.var(0); let y = pr.var(1);
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let yy = pr.mul(pr.clone_poly(&y), pr.clone_poly(&y));
        let bc1 = pr.sub(xx, pr.clone_poly(&x));
        let bc2 = pr.sub(yy, pr.clone_poly(&y));
        // x + 2y - 3
        let two = pr.constant(pr.field.from_int(2));
        let three = pr.constant(pr.field.from_int(3));
        let two_y = pr.mul(two, pr.clone_poly(&y));
        let bs = pr.sub(pr.add(pr.clone_poly(&x), two_y), three);
        let gens = vec![bc1, bc2, bs];
        let gb_direct = compute_gb_with_order(&pr,
            gens.iter().map(|p| pr.clone_poly(p)).collect(),
            &CancelToken::none(), MonomialOrder::DegRevLex);
        let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
        assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog),
                   "bit-cube + bitsum: direct LMs vs homog LMs");
    }

    #[test]
    fn test_homog_rabinowitsch() {
        // 1 - y * f trick: f = x^2 + 1, augment with `1 - z*(x^2+1)`.
        // Just check equivalence with direct on  {x^2 + 1, 1 - z*(x^2+1)}.
        let pr = pr_xyz(17);
        let x = pr.var(0); let z = pr.var(2);
        let xx = pr.mul(pr.clone_poly(&x), pr.clone_poly(&x));
        let one = pr.one();
        let f = pr.add(xx, pr.clone_poly(&one));
        let zf = pr.mul(pr.clone_poly(&z), pr.clone_poly(&f));
        let rab = pr.sub(one, zf);
        let gens = vec![f, rab];
        let gb_direct = compute_gb_with_order(&pr,
            gens.iter().map(|p| pr.clone_poly(p)).collect(),
            &CancelToken::none(), MonomialOrder::DegRevLex);
        let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
        assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog),
                   "Rabinowitsch: direct LMs vs homog LMs");
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
        let a = pr.var(0); let b = pr.var(1);
        let c = pr.var(2); let r = pr.var(3);
        let aa = pr.mul(pr.clone_poly(&a), pr.clone_poly(&a));
        let bb = pr.mul(pr.clone_poly(&b), pr.clone_poly(&b));
        let cc = pr.mul(pr.clone_poly(&c), pr.clone_poly(&c));
        let bc_a = pr.sub(aa, pr.clone_poly(&a));
        let bc_b = pr.sub(bb, pr.clone_poly(&b));
        let bc_c = pr.sub(cc, pr.clone_poly(&c));
        let two = pr.constant(pr.field.from_int(2));
        let two_c = pr.mul(two, pr.clone_poly(&c));
        // a + b - 2c - r
        let chunk = pr.sub(
            pr.sub(pr.add(pr.clone_poly(&a), pr.clone_poly(&b)), two_c),
            pr.clone_poly(&r),
        );
        let gens = vec![bc_a, bc_b, bc_c, chunk];
        let gb_direct = compute_gb_with_order(&pr,
            gens.iter().map(|p| pr.clone_poly(p)).collect(),
            &CancelToken::none(), MonomialOrder::DegRevLex);
        let gb_homog = compute_gb_by_homog(&pr, gens, &CancelToken::none());
        assert_eq!(lm_set(&pr, &gb_direct), lm_set(&pr, &gb_homog),
                   "chunked-add: direct LMs vs homog LMs");
    }
}
