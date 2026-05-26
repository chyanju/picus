//! Linear (Gaussian) pre-elimination — the in-tree analogue of cvc5's
//! `theory/ff/gauss.cpp`.
//!
//! The split-GB partition admits a polynomial into the nonlinear basis
//! only when it is linear AND has `<= 2` terms (`split_gb::admit`), so a
//! multi-term linear relation such as `x = a·y + b·z + c` never reaches
//! the nonlinear reasoning — its eliminations are stranded in basis 0.
//! This pass closes that gap: it computes a Gröbner basis of the linear
//! subsystem (for a linear ideal this is Gaussian elimination — a reduced
//! row echelon form) and reduces every nonlinear generator modulo it, so
//! the pivot variables are substituted out before split-GB runs.
//!
//! Soundness: the linear GB `L` generates the same ideal as the linear
//! inputs, and each nonlinear `p` is replaced by its normal form
//! `p mod L`, with `p ≡ (p mod L)` modulo `L`. Hence
//! `{L} ∪ {p mod L : p nonlinear}` and the original system define the
//! same variety over any prime field — a model of one is a model of the
//! other. (The caller still verifies any SAT model against the original
//! polynomials.) Linear inconsistency (`1 ∈ L`) is reported directly.

use crate::gb::ideal::Ideal;
use crate::poly::{FfPolyRing, Poly};
use crate::timeout::{CancelToken, Cancelled};

/// Result of [`eliminate_linear`].
pub struct LinElim {
    /// The reduced generator set: the linear Gröbner basis followed by
    /// each nonlinear generator reduced modulo it (zeros dropped).
    pub reduced: Vec<Poly>,
    /// True iff the input contained at least one linear polynomial, so
    /// `reduced` has been reordered/substituted relative to the input
    /// (an index into `reduced` no longer maps to an input index).
    pub applied: bool,
    /// True iff the linear subsystem alone is unsatisfiable (`1 ∈ L`).
    pub unsat: bool,
    /// Number of linear Gröbner-basis elements (pivot variables).
    pub n_eliminated: usize,
}

#[inline]
fn is_linear(p: &Poly) -> bool {
    p.total_degree() as usize <= 1
}

/// Eliminate the linear part of `polys` by Gaussian elimination and
/// substitute the result into the nonlinear part. See the module docs.
pub fn eliminate_linear<'r>(
    poly_ring: &'r FfPolyRing,
    polys: &[Poly],
    cancel: &CancelToken,
) -> Result<LinElim, Cancelled> {
    let mut linear: Vec<Poly> = Vec::new();
    let mut nonlinear: Vec<Poly> = Vec::new();
    for p in polys {
        if poly_ring.is_zero(p) {
            continue;
        }
        if is_linear(p) {
            linear.push(poly_ring.ring.clone_el(p));
        } else {
            nonlinear.push(poly_ring.ring.clone_el(p));
        }
    }

    // Skip when there is nothing to gain — no linear relations to use,
    // or no nonlinear generators to substitute them into. An all-linear
    // system is handled directly by the GB engine (which also yields a
    // precise UNSAT core), so we pass the input through unchanged,
    // preserving the caller's index → input-poly mapping and core tracing.
    if linear.is_empty() || nonlinear.is_empty() {
        return Ok(LinElim {
            reduced: polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect(),
            applied: false,
            unsat: false,
            n_eliminated: 0,
        });
    }

    let lin_ideal = Ideal::new_with_cancel(poly_ring, linear, cancel)?;
    if lin_ideal.is_whole_ring() {
        return Ok(LinElim { reduced: Vec::new(), applied: true, unsat: true, n_eliminated: 0 });
    }

    let n_eliminated = lin_ideal.basis.iter().filter(|p| !p.is_zero()).count();
    let mut reduced: Vec<Poly> = Vec::with_capacity(lin_ideal.basis.len() + nonlinear.len());
    for p in &lin_ideal.basis {
        reduced.push(poly_ring.ring.clone_el(p));
    }
    for nl in &nonlinear {
        if cancel.is_cancelled() {
            return Err(Cancelled);
        }
        let r = lin_ideal.reduce_with_cancel(nl, cancel);
        if !poly_ring.is_zero(&r) {
            reduced.push(r);
        }
    }

    Ok(LinElim { reduced, applied: true, unsat: false, n_eliminated })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use num_bigint::BigUint;

    fn ff(p: u32) -> PrimeField {
        PrimeField::new(BigUint::from(p))
    }

    #[test]
    fn no_linear_is_identity() {
        // Single nonlinear poly: x*y - 1. No linear polys → pass-through.
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let p = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
        let elim = eliminate_linear(&pr, &[p], &CancelToken::none()).unwrap();
        assert!(!elim.applied);
        assert_eq!(elim.reduced.len(), 1);
        assert_eq!(elim.n_eliminated, 0);
    }

    #[test]
    fn inconsistent_linear_is_unsat() {
        // x = 0 ∧ x = 1 over GF(7): linear subsystem alone is UNSAT.
        // A nonlinear generator (x*y) is included so the pass actually
        // runs (it is skipped for all-linear systems).
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let p1 = pr.var(0);
        let p2 = pr.sub(pr.var(0), pr.one());
        let p3 = pr.mul(pr.var(0), pr.var(1));
        let elim = eliminate_linear(&pr, &[p1, p2, p3], &CancelToken::none()).unwrap();
        assert!(elim.unsat);
    }

    #[test]
    fn linear_relation_substituted_into_nonlinear() {
        // GF(7): x - 3 = 0 (linear, pins x=3) and x*y - 1 = 0 (nonlinear).
        // After elimination the nonlinear poly must no longer mention x:
        // x*y - 1 reduces to 3*y - 1.
        let pr = FfPolyRing::new(ff(7), vec!["x".into(), "y".into()]);
        let three = pr.field().from_int(3);
        let lin = pr.sub(pr.var(0), pr.constant(three));
        let nl = pr.sub(pr.mul(pr.var(0), pr.var(1)), pr.one());
        let elim = eliminate_linear(&pr, &[lin, nl], &CancelToken::none()).unwrap();
        assert!(elim.applied);
        assert_eq!(elim.n_eliminated, 1);
        // Substitution happened: besides the pivot definition (x - 3,
        // which necessarily mentions x), at least one reduced poly is a
        // non-constant in y alone — the substituted x*y - 1 → 3*y - 1.
        let substituted = elim.reduced.iter().any(|p| {
            let vars = pr.ring.appearing_indeterminates(p);
            !vars.is_empty() && vars.iter().all(|v| v != 0)
        });
        assert!(substituted, "x must be substituted out of the nonlinear poly");
        // The variety is preserved: x=3, y=5 satisfies both original
        // polys (3*5=15≡1 mod 7), and must satisfy every reduced poly.
        let assign = |v: usize| -> BigUint {
            match v { 0 => BigUint::from(3u32), _ => BigUint::from(5u32) }
        };
        for p in &elim.reduced {
            let mut acc = pr.field().zero();
            for (c, m) in pr.ring.terms(p) {
                let mut term = pr.field().clone_el(c);
                for v in 0..pr.n_vars() {
                    let e = pr.ring.exponent_at(&m, v);
                    if e > 0 {
                        let val = pr.field().from_biguint(&assign(v));
                        term = pr.field().mul(&term, &pr.field().pow_u64(&val, e as u64));
                    }
                }
                acc = pr.field().add(&acc, &term);
            }
            assert!(pr.field().is_zero(&acc), "reduced poly must vanish at the witness");
        }
    }
}
