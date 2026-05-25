//! FGLM Gröbner-basis order conversion (Faugère–Gianni–Lazard–Mora, 1993).
//!
//! Converts a Gröbner basis of a **zero-dimensional** ideal from its source
//! order (here DegRevLex) to a target order (Lex) by linear algebra in the
//! finite-dimensional quotient ring `R/I`, instead of re-running Buchberger
//! from scratch in the target order. cvc5/CoCoA reach a lex/elimination
//! basis the same way; picus previously recomputed the Lex GB with a second
//! Buchberger pass (`gb::compute_gb_with_timeout` Phase 2).
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
use crate::poly::Poly;

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
pub fn fglm_to_lex(ideal: &Ideal) -> Option<Vec<Poly>> {
    let pr = ideal.poly_ring;
    let f = &pr.field;
    let ctx = pr.ctx();

    if ideal.is_whole_ring() {
        return Some(vec![pr.one()]);
    }
    if !ideal.is_zero_dim() {
        return None;
    }

    let n = pr.n_vars;
    let mono_poly = |m: &Monomial| pr.ring.create_term(f.one(), m.clone());
    // Coefficient of `mono` in `p` (0 if absent). `Monomial`'s equality is
    // raw-exponent equality, which is what we want here.
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

    Some(lex_gb)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::gb::ideal::{compute_gb_with_order, Ideal};
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
        let f = &pr.field;
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
        let mut v: Vec<_> = gb.iter().filter(|p| !pr.is_zero(p)).map(|p| canon(pr, p)).collect();
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
        let c = |v: i64| pr.constant(pr.field.from_int(v));
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
            pr.sub(x2, pr.constant(pr.field.from_int(5))),
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
    }
}
