//! FGLM Gröbner-basis order conversion (Faugère–Gianni–Lazard–Mora, 1993).
//!
//! Converts a Gröbner basis of a **zero-dimensional** ideal from its source
//! order (here DegRevLex) to a target order (Lex) by linear algebra in the
//! finite-dimensional quotient ring `R/I`, instead of re-running Buchberger
//! from scratch in the target order.
//!
//! Algorithm. Walk target-order monomials in increasing order from `1`.
//! For each `m` not already a multiple of a discovered leading term, take
//! the normal form `NF(m)` (reduction modulo the source GB). Reduce `NF(m)`
//! against the echelon of the normal forms of the staircase monomials found
//! so far (the same echelon-on-normal-forms used by `Ideal::min_poly`,
//! generalised from powers of one variable to all monomials):
//!   * dependent — `NF(m) = Σ cₖ·NF(bₖ)` — emit the new lex GB element
//!     `m − Σ cₖ·bₖ ∈ I`;
//!   * independent — `m` is a new quotient-basis (staircase) monomial; record
//!     its echelon row and enqueue the successors `xₖ·m`.
//! Terminates when the queue drains (the staircase reaches `dim R/I`).
//!
//! Only sound for zero-dimensional ideals; [`fglm_to_lex`] returns `None`
//! otherwise so the caller falls back to a direct Lex Buchberger run.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use crate::ff::field::FieldElem;
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::gb::ideal::Ideal;
use crate::metric;
use crate::poly::Poly;
use crate::timeout::CancelToken;

/// Candidate monomial ordered by the target (Lex) order, for the BFS queue.
#[derive(Clone)]
struct LexKey(Monomial);

impl PartialEq for LexKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.exponents() == other.0.exponents()
    }
}
impl Eq for LexKey {}
impl Ord for LexKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp_with_order(&other.0, MonomialOrder::Lex)
    }
}
impl PartialOrd for LexKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Safety cap on the number of monomials processed, mirroring
/// `min_poly`'s degree cap: guards against a non-terminating walk if the
/// zero-dimensional precondition is ever violated by a caller bug.
const FGLM_MONO_CAP: usize = 200_000;

/// Convert the (reduced) Gröbner basis held by `ideal` to a reduced Lex
/// Gröbner basis via FGLM. Returns `None` if the ideal is not
/// zero-dimensional (the caller should fall back to direct computation).
///
/// Uncancellable variant; for cancel-aware callers use
/// [`fglm_to_lex_cancel`].
pub fn fglm_to_lex(ideal: &Ideal) -> Option<Vec<Poly>> {
    fglm_to_lex_cancel(ideal, &CancelToken::none())
}

/// Cancel-aware FGLM: same as [`fglm_to_lex`] but bails out with `None`
/// when `cancel` fires mid-walk (large staircases on big primes can
/// otherwise run for seconds before the BFS queue drains).
pub fn fglm_to_lex_cancel(ideal: &Ideal, cancel: &CancelToken) -> Option<Vec<Poly>> {
    let pr = ideal.poly_ring;
    let f = &pr.field();
    let ctx = pr.ctx();

    if ideal.is_whole_ring() {
        return Some(vec![pr.one()]);
    }
    if !ideal.is_zero_dim() {
        return None;
    }

    let n = pr.n_vars();
    let mono_poly = |m: &Monomial| pr.ring.create_term(f.one(), m.clone());
    // Coefficient of `mono` in `p` (0 if absent). `Monomial` equality is
    // raw-exponent equality.
    let coeff_at = |p: &Poly, mono: &Monomial| -> FieldElem {
        for (c, m) in pr.ring.terms(p) {
            if m.exponents() == mono.exponents() {
                return f.clone_el(c);
            }
        }
        f.zero()
    };

    // Output: lex GB elements and their leading monomials.
    let mut lex_gb: Vec<Poly> = Vec::new();
    let mut lex_lts: Vec<Monomial> = Vec::new();

    // Echelon of staircase normal forms (parallel to `min_poly`):
    //   nfs[i]   — reduced NF poly, pivot = its leading monomial,
    //   pivots[i]— that leading monomial,
    //   deps[i]  — combination over the staircase such that
    //              nfs[i] = Σ deps[i][k]·NF(staircase[k]).
    let mut staircase: Vec<Monomial> = Vec::new();
    let mut nfs: Vec<Poly> = Vec::new();
    let mut pivots: Vec<Monomial> = Vec::new();
    let mut deps: Vec<Vec<FieldElem>> = Vec::new();

    // BFS queue of candidate monomials in increasing Lex order, seeded with 1.
    let mut queue: BTreeSet<LexKey> = BTreeSet::new();
    queue.insert(LexKey(Monomial::from_exponents(vec![0u16; n])));

    let mut processed = 0usize;
    while let Some(key) = queue.iter().next().cloned() {
        if cancel.is_cancelled() {
            return None;
        }
        queue.remove(&key);
        let m = key.0;
        processed += 1;
        if processed > FGLM_MONO_CAP {
            return None;
        }

        // Skip monomials already reducible by a discovered lex leading term.
        if lex_lts.iter().any(|lt| lt.divides(&m)) {
            continue;
        }

        let nf = ideal.reduce(&mono_poly(&m));

        // Reduce NF(m) against the echelon, accumulating the staircase
        // combination in `comb` (length = current staircase size).
        let mut row = nf;
        let mut comb: Vec<FieldElem> = vec![f.zero(); staircase.len()];
        for i in 0..nfs.len() {
            let c = coeff_at(&row, &pivots[i]);
            if !f.is_zero(&c) {
                let lc = coeff_at(&nfs[i], &pivots[i]);
                let factor = f.div(&c, &lc).expect("pivot coefficient is nonzero");
                let scaled = pr.scale(f.neg(&factor), pr.ring.clone_el(&nfs[i]));
                row = pr.add(row, scaled);
                for k in 0..deps[i].len() {
                    let prod = f.mul(&factor, &deps[i][k]);
                    f.add_assign(&mut comb[k], prod);
                }
            }
        }

        if pr.is_zero(&row) {
            // NF(m) = Σ comb[k]·NF(staircase[k])  ⇒  m − Σ comb[k]·bₖ ∈ I.
            let mut g = mono_poly(&m);
            for k in 0..staircase.len() {
                if !f.is_zero(&comb[k]) {
                    let term = pr.scale(f.clone_el(&comb[k]), mono_poly(&staircase[k]));
                    g = pr.sub(g, term);
                }
            }
            lex_gb.push(g);
            lex_lts.push(m);
        } else {
            // Independent: `m` joins the staircase. Its echelon row is the
            // reduced `row`; record the combination expressing it over the
            // new staircase (coefficient 1 on `m`, −comb on the rest).
            let pivot = row
                .leading_monomial(ctx)
                .expect("non-zero row has a leading monomial");
            let mut dep_new: Vec<FieldElem> = comb.iter().map(|c| f.neg(c)).collect();
            dep_new.push(f.one());
            staircase.push(m.clone());
            nfs.push(row);
            pivots.push(pivot);
            deps.push(dep_new);
            for k in 0..n {
                let mut exps = m.exponents().to_vec();
                exps[k] += 1;
                queue.insert(LexKey(Monomial::from_exponents(exps)));
            }
        }
    }

    // Sound cross-check: the staircase is a k-basis of R/I, so its size
    // equals dim_k(R/I) read independently off the leading-term ideal via
    // the Hilbert function (`crate::ff::hilbert`). A mismatch means the
    // FGLM combination accounting is inconsistent — rather than trust a lex
    // basis that may not lie in I, return None so the caller falls back to
    // direct Buchberger Lex (sound). Runs in release, not just debug.
    let hilbert_dim = ideal.quotient_dimension();
    metric::scope! {
        eprintln!(
            "[picus-gb-stats] fglm_dim={} hilbert_dim={:?}",
            staircase.len(),
            hilbert_dim
        );
    }
    if hilbert_dim != Some(staircase.len() as u128) {
        log::warn!(
            "FGLM staircase size {} disagrees with Hilbert dimension {:?}; \
             falling back to direct Lex",
            staircase.len(),
            hilbert_dim
        );
        return None;
    }

    Some(lex_gb)
}

#[cfg(test)]
#[path = "fglm_tests.rs"]
mod tests;
