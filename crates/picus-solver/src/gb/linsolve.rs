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
    // Fail-closed: `compute_gb_with_order` returns an empty basis on a
    // genuine engine error (panic / internal failure caught by `finish_gb`),
    // and a non-empty linear input cannot legitimately yield an empty basis
    // without cancellation. Proceeding with the elimination here would
    // silently drop every linear constraint and the substituted nonlinear
    // generators reach the solver as the entire system; the downstream
    // `verify_model` then checks against this reduced set (not the input),
    // letting a model that satisfies only the nonlinear part be reported
    // as SAT. Fall back to passing the input through unchanged so the GB
    // engine sees the full system and `verify_model` gates correctly.
    if lin_ideal.basis.is_empty() {
        return Ok(LinElim {
            reduced: polys.iter().map(|p| poly_ring.ring.clone_el(p)).collect(),
            applied: false,
            unsat: false,
            n_eliminated: 0,
        });
    }
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
#[path = "linsolve_tests.rs"]
mod tests;
