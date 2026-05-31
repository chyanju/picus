//! GVW (Gao–Volny–Wang) signature-based Gröbner basis with
//! signature-safe reduction — the engine path used when
//! `signature_criterion` is on.
//!
//! The per-pair Buchberger loop discovers a zero-reduction only after
//! paying its full cost. GVW instead carries a Schreyer signature on every
//! labeled polynomial and J-pair, reduces *signature-safely* (only by a
//! reducer that strictly lowers the signature), and skips a J-pair whose
//! signature a recorded syzygy proves redundant or whose signature an
//! already-admitted basis element already represents. A skipped J-pair is
//! guaranteed to reduce to zero, so the zero-reductions the classical
//! product / Gebauer-Möller / Buchberger criteria fail to predict are
//! eliminated outright rather than reduced-then-discarded.
//!
//! Self-contained over `DensePoly`; the per-pair engine is untouched. The
//! output polynomials form a Gröbner basis of the input ideal in `order`;
//! the caller interreduces to the reduced GB. Soundness is pinned by the
//! `signature_gb_matches_per_pair_*` differential oracle (the GVW basis
//! must equal the per-pair reduced GB) plus `verify_model`.

use std::cmp::Ordering;

use crate::ff::field::FieldElem;
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{DensePoly, PolyRing};
use crate::timeout::CancelToken;
use crate::EngineError;

use super::signature::Signature;

/// A polynomial tagged with its Schreyer signature and cached leading term.
struct Labeled {
    sig: Signature,
    poly: DensePoly,
    lm: Monomial,
    lc: FieldElem,
}

/// A J-pair: the signature-labeled analogue of an S-pair. `sig` is the
/// larger of the two parents' cofactor signatures; `src` is the basis
/// index of the parent that contributed it (used by the rewrite criterion);
/// `lcm` is the leading-monomial lcm used to build the S-polynomial.
struct JPair {
    sig: Signature,
    i: usize,
    j: usize,
    src: usize,
    lcm: Monomial,
}

fn check(cancel: Option<&CancelToken>) -> Result<(), EngineError> {
    if let Some(c) = cancel {
        if c.is_cancelled() {
            return Err(EngineError::Timeout);
        }
    }
    Ok(())
}

/// S-polynomial of two labeled polynomials at their leading-monomial lcm
/// (the classical S-poly; mirrors `BuchbergerState::build_spoly`).
fn build_spoly(a: &Labeled, b: &Labeled, lcm: &Monomial, ring: &PolyRing) -> DensePoly {
    let field = &ring.field;
    let mul_a = lcm.div(&a.lm);
    let mul_b = lcm.div(&b.lm);
    let one = field.one();
    let part_a = a.poly.mul_term(mul_a.exponents(), &one, ring);
    let scale_b = field.div(&a.lc, &b.lc).expect("nonzero leading coeff");
    let part_b = b.poly.mul_term(mul_b.exponents(), &scale_b, ring);
    part_a.sub(&part_b, ring)
}

/// Signature-safe top-reduction of `poly` (which carries signature `sig`):
/// repeatedly cancel the leading term using a basis element whose leading
/// monomial divides it AND whose reduced signature is strictly below `sig`.
/// Stops when the leading term is signature-irreducible (or `poly` is 0).
fn sig_reduce(
    mut poly: DensePoly,
    sig: &Signature,
    basis: &[Labeled],
    ring: &PolyRing,
    order: MonomialOrder,
    cancel: Option<&CancelToken>,
) -> Result<DensePoly, EngineError> {
    let field = &ring.field;
    loop {
        if poly.is_zero() {
            return Ok(poly);
        }
        let plm = poly.leading_monomial(ring).expect("nonzero poly has LT");
        let plc = field.clone_el(poly.leading_coefficient().expect("nonzero poly has LC"));
        let mut reduced = false;
        for b in basis {
            if !b.lm.divides(&plm) {
                continue;
            }
            let factor = plm.div(&b.lm);
            // Signature-safe: only reduce if the reducer cannot raise the
            // signature to/above the current one.
            if b.sig.mul(&factor).cmp(sig, order) != Ordering::Less {
                continue;
            }
            let coeff = field.div(&plc, &b.lc).expect("nonzero reducer LC");
            let term = b.poly.mul_term(factor.exponents(), &coeff, ring);
            poly = poly.sub(&term, ring);
            reduced = true;
            break;
        }
        if !reduced {
            return Ok(poly);
        }
        check(cancel)?;
    }
}

/// J-pair of basis elements `a`, `b` (a < b). Returns `None` when the two
/// cofactor signatures are equal (a singular pair — a syzygy carrying no
/// new signature).
fn make_jpair(a: usize, b: usize, basis: &[Labeled], order: MonomialOrder) -> Option<JPair> {
    let la = &basis[a];
    let lb = &basis[b];
    let lcm = la.lm.lcm(&lb.lm);
    let sa = la.sig.mul(&lcm.div(&la.lm));
    let sb = lb.sig.mul(&lcm.div(&lb.lm));
    match sa.cmp(&sb, order) {
        Ordering::Equal => None,
        Ordering::Greater => Some(JPair { sig: sa, i: a, j: b, src: a, lcm }),
        Ordering::Less => Some(JPair { sig: sb, i: a, j: b, src: b, lcm }),
    }
}

/// Compute a Gröbner basis of `generators` in `order` via GVW. The result
/// is a (not necessarily reduced) GB; the caller interreduces.
pub(crate) fn groebner_basis_gvw(
    generators: Vec<DensePoly>,
    ring: &PolyRing,
    order: MonomialOrder,
    cancel: Option<&CancelToken>,
) -> Result<Vec<DensePoly>, EngineError> {
    let field = &ring.field;
    let n_vars = ring.n_vars;

    let mut basis: Vec<Labeled> = Vec::new();
    // Recorded syzygy leading monomials, per signature index.
    let mut syz: Vec<Vec<Monomial>> = Vec::new();
    let mut queue: Vec<JPair> = Vec::new();

    // Seed the basis with the input generators; generator i has signature
    // (i, 1). A leading-constant generator makes the ideal the whole ring.
    for (i, g) in generators.into_iter().enumerate() {
        while syz.len() <= i {
            syz.push(Vec::new());
        }
        if g.is_zero() {
            continue;
        }
        let lm = g.leading_monomial(ring).expect("nonzero poly has LT");
        let lc = field.clone_el(g.leading_coefficient().expect("nonzero poly has LC"));
        if lm.is_one() {
            // Whole ring — return the unit immediately.
            return Ok(vec![g]);
        }
        let new = basis.len();
        let sig = Signature::input(i as u32, n_vars);
        basis.push(Labeled { sig, poly: g, lm, lc });
        for k in 0..new {
            if let Some(jp) = make_jpair(k, new, &basis, order) {
                queue.push(jp);
            }
        }
    }

    let mut guard: u64 = 0;
    let guard_cap: u64 = 50_000_000;
    while !queue.is_empty() {
        check(cancel)?;
        guard += 1;
        if guard > guard_cap {
            return Err(EngineError::Timeout);
        }

        // Pop the J-pair with the smallest signature (GVW processes in
        // increasing signature order — required for the criteria to be
        // sound).
        let mut min = 0usize;
        for k in 1..queue.len() {
            if queue[k].sig.cmp(&queue[min].sig, order) == Ordering::Less {
                min = k;
            }
        }
        let jp = queue.swap_remove(min);
        let idx = jp.sig.idx as usize;

        // Syzygy (F5) criterion: a recorded syzygy signature divides this
        // one ⇒ guaranteed zero-reduction, skip.
        if idx < syz.len() && syz[idx].iter().any(|h| h.divides(&jp.sig.monom)) {
            continue;
        }
        // Rewrite criterion (GVW): a basis element added after this J-pair's
        // source carries a signature dividing it ⇒ a better representative
        // of the same signature exists, so this pair is redundant. This is
        // what keeps GVW from a combinatorial blow-up of redundant pairs.
        if basis[jp.src + 1..].iter().any(|b| b.sig.divides(&jp.sig)) {
            continue;
        }

        let s = build_spoly(&basis[jp.i], &basis[jp.j], &jp.lcm, ring);
        let nf = sig_reduce(s, &jp.sig, &basis, ring, order, cancel)?;

        if nf.is_zero() {
            // New syzygy: record its leading signature monomial.
            while syz.len() <= idx {
                syz.push(Vec::new());
            }
            syz[idx].push(jp.sig.monom.clone());
            continue;
        }

        let lm = nf.leading_monomial(ring).expect("nonzero poly has LT");
        // Singular criterion: an existing basis element with the same
        // signature whose leading monomial divides this one already
        // represents this signature ⇒ redundant, skip. (Checked AFTER the
        // regular reduction, on the reduced leading term — a same-signature
        // reduction that lowers the leading term is NOT singular and must be
        // admitted.)
        if basis.iter().any(|b| b.sig == jp.sig && b.lm.divides(&lm)) {
            continue;
        }
        let lc = field.clone_el(nf.leading_coefficient().expect("nonzero poly has LC"));
        if lm.is_one() {
            return Ok(vec![nf]);
        }
        let new = basis.len();
        basis.push(Labeled { sig: jp.sig, poly: nf, lm, lc });
        for k in 0..new {
            if let Some(jp2) = make_jpair(k, new, &basis, order) {
                queue.push(jp2);
            }
        }
    }

    Ok(basis.into_iter().map(|b| b.poly).collect())
}

#[cfg(test)]
#[path = "gvw_tests.rs"]
mod tests;
