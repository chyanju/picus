//! Gröbner basis on the sparse polynomial representation.
//!
//! Buchberger's algorithm over [`SparsePolynomial`] with the same pruning
//! the dense engine applies: Buchberger's product (coprime) criterion and
//! the Gebauer-Möller M-criterion at pair generation, the B-criterion at
//! basis-add, and a sugar-degree priority queue for pair selection. The
//! M / B criteria and the descending merge are the shared,
//! representation-generic [`super::spair_criteria`] functions; the sparse
//! S-pair supplies a presence-based DivMask ([`SparseMonomial::divmask`])
//! for the prefilter.
//!
//! The reduced Gröbner basis of an ideal under a fixed monomial order is
//! unique, so the criteria (which only change *which* S-pairs are
//! processed, never the final ideal) leave the result identical to the
//! dense engine's; `repr_oracle` checks that term-for-term.

use crate::ff::spair_criteria::{b_criterion_kill, gm_insert, merge_sorted_descending};
use crate::timeout::CancelToken;

use super::divmask::DivMask;
use super::polynomial::PolyRing;
use super::repr::MonomialRepr;
use super::sparse_monomial::SparseMonomial;
use super::sparse_polynomial::SparsePolynomial;

// ─────────────────────────────── S-polynomial ──────────────────────────────

/// Monic-normalised S-polynomial of two nonzero polynomials:
/// `(1/lc(f))·(L/lm(f))·f − (1/lc(g))·(L/lm(g))·g`, `L = lcm(lm(f), lm(g))`.
pub fn s_polynomial(
    f: &SparsePolynomial,
    g: &SparsePolynomial,
    ring: &PolyRing,
) -> SparsePolynomial {
    let (lmf, lcf) = f.leading_term().expect("s_polynomial: f is nonzero");
    let (lmg, lcg) = g.leading_term().expect("s_polynomial: g is nonzero");
    let l = MonomialRepr::lcm(lmf, lmg);
    let mf = MonomialRepr::div(&l, lmf);
    let mg = MonomialRepr::div(&l, lmg);
    let inv_f = ring.field.inv(lcf).expect("nonzero leading coeff");
    let inv_g = ring.field.inv(lcg).expect("nonzero leading coeff");
    let term_f = SparsePolynomial::from_terms(vec![(mf, inv_f)], ring);
    let term_g = SparsePolynomial::from_terms(vec![(mg, inv_g)], ring);
    let part_f = term_f.mul(f, ring);
    let part_g = term_g.mul(g, ring);
    part_f.sub(&part_g, ring)
}

// ──────────────────────────── S-pair + criteria ────────────────────────────

/// A critical S-pair. Mirrors [`super::spair::SPair`]; the `generation`
/// tag (dense incremental driver) is omitted, and `lcm_divmask` is the
/// presence-based sparse DivMask rather than the dense threshold scheme.
#[derive(Clone, Debug)]
struct SPair {
    i: usize,
    j: usize,
    sugar: u32,
    lcm: SparseMonomial,
    /// Presence DivMask of `lcm`, for O(1) divisibility rejection in the
    /// M / B criteria before the full monomial check.
    lcm_divmask: DivMask,
    lcm_deg: u32,
    age: u64,
}

impl SPair {
    /// `(sugar, lcm_deg, age)`; smaller is selected first.
    #[inline]
    fn ordering_key(&self) -> (u32, u32, u64) {
        (self.sugar, self.lcm_deg, self.age)
    }
}

impl super::spair_criteria::CriterionPair for SPair {
    type Mono = SparseMonomial;
    fn lcm(&self) -> &SparseMonomial {
        &self.lcm
    }
    fn lcm_divmask(&self) -> DivMask {
        self.lcm_divmask
    }
    /// Coprime pairs never reach `gm_insert` here (the product criterion
    /// drops them at generation), so the same-lcm coprime-replacement
    /// branch in the shared `gm_insert` must stay inert.
    fn is_coprime(&self) -> bool {
        false
    }
    fn parents(&self) -> (usize, usize) {
        (self.i, self.j)
    }
    fn cmp_key(&self) -> (u32, u32, u64) {
        self.ordering_key()
    }
}

// ──────────────────────────────── Buchberger ───────────────────────────────

/// Internal basis element: the polynomial, its cached leading monomial,
/// the lazy-deactivation flag, and the sugar degree at insertion.
struct BasisElement {
    poly: SparsePolynomial,
    lt: SparseMonomial,
    active: bool,
    sugar: u32,
}

impl super::spair_criteria::LeadingTerms for Vec<BasisElement> {
    type Mono = SparseMonomial;
    fn lt_at(&self, idx: usize) -> &SparseMonomial {
        &self[idx].lt
    }
}

/// Stateful sparse Buchberger run. Mirrors the dense
/// `buchberger::BuchbergerState` shape: a basis with non-strict
/// deactivation, a sugar-ordered open queue (`open` is sorted descending
/// so `pop()` returns the smallest pair), and pair-generation that applies
/// the product / M / B criteria.
struct Buchberger<'a> {
    ring: &'a PolyRing,
    cancel: Option<&'a CancelToken>,
    basis: Vec<BasisElement>,
    /// Pending S-pairs, sorted **descending** by `ordering_key` so
    /// `Vec::pop()` yields the smallest (lowest sugar, then lcm_deg, then
    /// age). A sorted vector, not a heap, because the M-criterion walks
    /// and mutates the list during insertion.
    open: Vec<SPair>,
    age_counter: u64,
    /// Set once a nonzero constant enters the basis: the ideal is the
    /// whole ring, so the reduced GB is `{1}`.
    trivial: bool,
}

impl<'a> Buchberger<'a> {
    fn new(ring: &'a PolyRing, cancel: Option<&'a CancelToken>) -> Self {
        Buchberger {
            ring,
            cancel,
            basis: Vec::new(),
            open: Vec::new(),
            age_counter: 0,
            trivial: false,
        }
    }

    #[inline]
    fn cancelled(&self) -> bool {
        self.cancel.is_some_and(|c| c.is_cancelled())
    }

    /// Seed the basis with a set that is already a reduced Gröbner basis in
    /// `ring.order`, skipping S-pair generation among the seed elements:
    /// a reduced GB has no open obligations among its own members (every
    /// S-pair reduces to zero), so `add_generators` of new polynomials need
    /// only process the cross / intra-new pairs. Mirrors the dense
    /// `BuchbergerState::seed_with_reduced_basis`. Caller asserts the input
    /// is a reduced GB; no validation is performed.
    fn seed_reduced_basis(&mut self, basis: Vec<SparsePolynomial>) {
        for poly in basis {
            if poly.is_zero() {
                continue;
            }
            if poly.is_constant() {
                // A reduced GB containing a constant is {1}: the whole ring.
                self.trivial = true;
                return;
            }
            let lt = poly.leading_monomial().unwrap().clone();
            let sugar = lt.total_degree();
            // Same non-strict deactivation as `integrate` (a no-op for a
            // proper reduced GB, whose leading terms are incomparable).
            let new_idx = self.basis.len();
            for k in 0..new_idx {
                if self.basis[k].active && MonomialRepr::divides(&lt, &self.basis[k].lt) {
                    self.basis[k].active = false;
                }
            }
            self.basis.push(BasisElement { poly, lt, active: true, sugar });
        }
    }

    /// Reduce each generator by the current basis, then integrate it:
    /// drop zeros, collapse to the trivial ideal on a constant, otherwise
    /// generate its S-pairs and add it (with non-strict deactivation).
    fn add_generators(&mut self, generators: Vec<SparsePolynomial>) {
        for g in generators {
            if self.cancelled() || self.trivial {
                return;
            }
            if g.is_zero() {
                continue;
            }
            let active_refs: Vec<&SparsePolynomial> =
                self.basis.iter().filter(|e| e.active).map(|e| &e.poly).collect();
            let g_red = g.reduce_by_refs_cancel(&active_refs, self.ring, self.cancel);
            if self.cancelled() {
                return;
            }
            if g_red.is_zero() {
                continue;
            }
            let g_red = g_red.make_monic(self.ring);
            if g_red.is_constant() {
                self.trivial = true;
                return;
            }
            let lt = g_red.leading_monomial().unwrap().clone();
            let sugar = lt.total_degree();
            self.integrate(g_red, lt, sugar);
        }
    }

    /// Push a new (already monic, non-constant) polynomial into the basis:
    /// generate its pairs against the active basis first (so pairs against
    /// soon-to-be-deactivated elements are not lost), then apply non-strict
    /// deactivation, then append.
    fn integrate(&mut self, poly: SparsePolynomial, lt: SparseMonomial, sugar: u32) {
        let new_idx = self.basis.len();
        self.generate_pairs_against(new_idx, &lt, sugar);
        for k in 0..new_idx {
            if self.basis[k].active && MonomialRepr::divides(&lt, &self.basis[k].lt) {
                self.basis[k].active = false;
            }
        }
        self.basis.push(BasisElement { poly, lt, active: true, sugar });
    }

    /// Build the pairs `(k, new_idx)` for every active `k < new_idx`,
    /// dropping coprime pairs (product criterion) and applying the
    /// M-criterion (`gm_insert`); prune the open queue with the
    /// B-criterion; merge the survivors in, keeping the descending sort.
    fn generate_pairs_against(&mut self, new_idx: usize, new_lt: &SparseMonomial, new_sugar: u32) {
        let new_lt_deg = new_lt.total_degree();
        let mut new_pairs: Vec<SPair> = Vec::new();
        for k in 0..new_idx {
            if !self.basis[k].active {
                continue;
            }
            let basis_k_lt = &self.basis[k].lt;
            if MonomialRepr::is_coprime(new_lt, basis_k_lt) {
                // Product criterion: coprime leading terms ⇒ the
                // S-polynomial reduces to zero via the generators.
                continue;
            }
            let lcm = MonomialRepr::lcm(new_lt, basis_k_lt);
            let lcm_deg = lcm.total_degree();
            let lcm_divmask = lcm.divmask();
            // Sugar = max over the two parents of deg(lcm/LT) + sugar(parent).
            let s_new = new_sugar + (lcm_deg - new_lt_deg);
            let s_k = self.basis[k].sugar + (lcm_deg - basis_k_lt.total_degree());
            let sugar = s_new.max(s_k);
            self.age_counter += 1;
            let pair = SPair { i: k, j: new_idx, sugar, lcm, lcm_divmask, lcm_deg, age: self.age_counter };
            gm_insert(&mut new_pairs, pair);
        }
        b_criterion_kill(&mut self.open, new_lt, new_lt.divmask(), &self.basis);
        new_pairs.sort_by(|a, b| b.ordering_key().cmp(&a.ordering_key()));
        merge_sorted_descending(&mut self.open, new_pairs);
    }

    /// Process pairs lowest-sugar-first until the queue drains: form each
    /// S-polynomial, reduce it by the active basis, and integrate a nonzero
    /// normal form (short-circuiting on a constant).
    fn run(&mut self) {
        if self.trivial {
            return;
        }
        while let Some(pair) = self.open.pop() {
            if self.cancelled() {
                return;
            }
            let s = s_polynomial(&self.basis[pair.i].poly, &self.basis[pair.j].poly, self.ring);
            let nf = {
                let active_refs: Vec<&SparsePolynomial> =
                    self.basis.iter().filter(|e| e.active).map(|e| &e.poly).collect();
                s.reduce_by_refs_cancel(&active_refs, self.ring, self.cancel)
            };
            // A reduction interrupted by cancellation returns a partial
            // normal form; bail before integrating it.
            if self.cancelled() {
                return;
            }
            if nf.is_zero() {
                continue;
            }
            let nf = nf.make_monic(self.ring);
            if nf.is_constant() {
                self.trivial = true;
                return;
            }
            let lt = nf.leading_monomial().unwrap().clone();
            // The pair sugar bounds the normal form's leading degree
            // (reduction is degree-non-increasing on the leading term).
            self.integrate(nf, lt, pair.sugar);
        }
    }

    /// The active basis (a Gröbner basis, not yet inter-reduced), or `{1}`
    /// when the ideal is the whole ring.
    fn into_basis(self) -> Vec<SparsePolynomial> {
        if self.trivial {
            return vec![SparsePolynomial::constant(self.ring.field.one(), self.ring)];
        }
        self.basis.into_iter().filter(|e| e.active).map(|e| e.poly).collect()
    }
}

/// A Gröbner basis of the ideal generated by `gens` (Buchberger with the
/// product / Gebauer-Möller M / B criteria and sugar selection). The result
/// is a — not necessarily reduced — Gröbner basis; call [`interreduce`] for
/// the canonical reduced form. On `cancel`, returns the basis built so far,
/// which generates a **sub-ideal** of the input (unprocessed generators are
/// dropped and any in-flight reduction halts mid-step); the caller must
/// check `is_cancelled()` before relying on the result.
pub fn groebner_basis(
    gens: Vec<SparsePolynomial>,
    ring: &PolyRing,
    cancel: Option<&CancelToken>,
) -> Vec<SparsePolynomial> {
    let mut b = Buchberger::new(ring, cancel);
    b.add_generators(gens);
    b.run();
    b.into_basis()
}

/// Incrementally extend a reduced Gröbner basis `known_gb` with
/// `new_gens`: seed the engine with `known_gb` (pair-free) and run
/// Buchberger only on the cross (`known_gb` × `new_gens`) and intra-new
/// S-pairs. The result is a Gröbner basis of the combined ideal — equal,
/// after [`interreduce`], to recomputing from scratch on the union (the
/// reduced GB is unique). `known_gb` must be a reduced GB in `ring.order`.
/// On `cancel`, returns the basis built so far, which generates a sub-ideal
/// of the combined ideal; the caller must check `is_cancelled()` before
/// relying on the result.
pub fn groebner_basis_incremental(
    known_gb: Vec<SparsePolynomial>,
    new_gens: Vec<SparsePolynomial>,
    ring: &PolyRing,
    cancel: Option<&CancelToken>,
) -> Vec<SparsePolynomial> {
    let mut b = Buchberger::new(ring, cancel);
    b.seed_reduced_basis(known_gb);
    b.add_generators(new_gens);
    b.run();
    b.into_basis()
}

/// Inter-reduce a basis into the canonical reduced Gröbner basis: drop
/// zeros, collapse to `{1}` if the ideal is the whole ring, make every
/// element monic, drop elements whose leading term is divisible by
/// another's, and tail-reduce each survivor by the others. Mirrors the
/// dense `buchberger::interreduce`. Returns the partially-reduced basis on
/// cancellation (still a valid generating set).
pub fn interreduce(
    mut basis: Vec<SparsePolynomial>,
    ring: &PolyRing,
    cancel: Option<&CancelToken>,
) -> Vec<SparsePolynomial> {
    basis.retain(|p| !p.is_zero());
    if basis.iter().any(|p| p.is_constant()) {
        return vec![SparsePolynomial::constant(ring.field.one(), ring)];
    }
    for p in basis.iter_mut() {
        *p = p.make_monic(ring);
    }
    // Sort by leading monomial descending (deterministic output).
    basis.sort_by(|a, b| {
        let la = a.leading_monomial().unwrap();
        let lb = b.leading_monomial().unwrap();
        MonomialRepr::cmp_with_order(lb, la, ring.order)
    });
    // Minimise: drop any element whose leading monomial is divisible by
    // another's. On equal leading monomials keep the lowest index, so
    // duplicate-LT elements (which dehomogenization can produce) are
    // de-duplicated rather than both kept.
    let mut keep = vec![true; basis.len()];
    for i in 0..basis.len() {
        if !keep[i] {
            continue;
        }
        let li = basis[i].leading_monomial().unwrap().clone();
        for j in 0..basis.len() {
            if i == j || !keep[j] {
                continue;
            }
            let lj = basis[j].leading_monomial().unwrap();
            if MonomialRepr::divides(&li, lj) && (&li != lj || j > i) {
                keep[j] = false;
            }
        }
    }
    let mut filtered: Vec<SparsePolynomial> = basis
        .into_iter()
        .zip(keep)
        .filter_map(|(p, k)| k.then_some(p))
        .collect();

    // Single-pass tail reduction (after minimisation no surviving LT
    // divides another's, so one pass reaches the reduced form).
    let n = filtered.len();
    for i in 0..n {
        if cancel.is_some_and(|c| c.is_cancelled()) {
            break;
        }
        let red = {
            let others: Vec<&SparsePolynomial> = filtered
                .iter()
                .enumerate()
                .filter(|(j, p)| *j != i && !p.is_zero())
                .map(|(_, p)| p)
                .collect();
            if others.is_empty() {
                None
            } else {
                Some(filtered[i].reduce_by_refs(&others, ring))
            }
        };
        if let Some(red) = red {
            filtered[i] = if red.is_zero() {
                SparsePolynomial::zero()
            } else {
                red.make_monic(ring)
            };
        }
    }
    filtered.retain(|p| !p.is_zero());
    filtered
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::ff::monomial::MonomialOrder;
    use num_bigint::BigUint;
    use std::sync::Arc;

    fn ring2() -> Arc<PolyRing> {
        PolyRing::new(
            PrimeField::new(BigUint::from(7u32)),
            vec!["x".into(), "y".into()],
            MonomialOrder::DegRevLex,
        )
    }

    // ────────── s_polynomial ──────────

    #[test]
    fn s_polynomial_of_coprime_pair_is_zero_after_reduction() {
        // f = x, g = y. lcm = x·y, S(f,g) = y·f − x·g = xy − xy = 0.
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let y = SparsePolynomial::variable(1, &ring);
        let s = s_polynomial(&x, &y, &ring);
        assert!(s.is_zero());
    }

    #[test]
    fn s_polynomial_of_x_and_xy_minus_1() {
        // f = x, g = x·y − 1.
        // lm(f) = x, lm(g) = x·y (under DegRevLex), lcm = x·y.
        // m_f = y, m_g = 1.
        // S(f,g) = y·x − 1·(x·y − 1) = xy − xy + 1 = 1 (constant).
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let xy = x.mul(&SparsePolynomial::variable(1, &ring), &ring);
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        let xy_minus_1 = xy.sub(&one, &ring);
        let s = s_polynomial(&x, &xy_minus_1, &ring);
        assert!(s.is_constant() && !s.is_zero());
    }

    // ────────── groebner_basis ──────────

    #[test]
    fn groebner_basis_of_unit_input_is_trivial() {
        let ring = ring2();
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        let gb = groebner_basis(vec![one], &ring, None);
        // Trivial ideal: {1}.
        assert!(gb.iter().any(|p| p.is_constant() && !p.is_zero()));
    }

    #[test]
    fn groebner_basis_of_empty_input_is_empty() {
        let ring = ring2();
        let gb = groebner_basis(vec![], &ring, None);
        assert!(gb.is_empty());
    }

    #[test]
    fn groebner_basis_of_xy_minus_1_yields_nonempty_basis() {
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let y = SparsePolynomial::variable(1, &ring);
        let xy = x.mul(&y, &ring);
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        let p = xy.sub(&one, &ring);
        let gb = groebner_basis(vec![p], &ring, None);
        assert!(!gb.is_empty());
        // Not the whole ring (1 ∈ I would mean x·y = 1 over GF(7) — has
        // solutions, so GB shouldn't collapse).
        assert!(!gb.iter().any(|p| p.is_constant() && !p.is_zero()));
    }

    // ────────── groebner_basis_incremental ──────────

    #[test]
    fn groebner_basis_incremental_matches_from_scratch_after_interreduce() {
        // Compute GB({x·y − 1}) from scratch vs incrementally as
        // (known: ∅, new: {x·y − 1}). After interreduce, equal as sets.
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let y = SparsePolynomial::variable(1, &ring);
        let xy = x.mul(&y, &ring);
        let one = SparsePolynomial::constant(ring.field.one(), &ring);
        let p = xy.sub(&one, &ring);

        let gb_scratch = interreduce(groebner_basis(vec![p.clone()], &ring, None), &ring, None);
        let gb_inc = interreduce(
            groebner_basis_incremental(vec![], vec![p], &ring, None),
            &ring,
            None,
        );
        assert_eq!(gb_scratch.len(), gb_inc.len());
    }

    // ────────── interreduce ──────────

    #[test]
    fn interreduce_drops_dominated_leading_term() {
        // {x, x·y} — x·y is divisible by x's leading term, so x·y is
        // either removed or reduced to zero. interreduce should collapse
        // to {x} (after monicization).
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let xy = x.mul(&SparsePolynomial::variable(1, &ring), &ring);
        let reduced = interreduce(vec![x.clone(), xy], &ring, None);
        assert_eq!(reduced.len(), 1);
    }

    #[test]
    fn interreduce_collapses_to_unit_on_whole_ring_basis() {
        // {x, 2} → 2 ≠ 0 (since GF(7)) ⇒ constant ⇒ whole ring ⇒ {1}.
        let ring = ring2();
        let x = SparsePolynomial::variable(0, &ring);
        let two = SparsePolynomial::constant(ring.field.from_int(2), &ring);
        let reduced = interreduce(vec![x, two], &ring, None);
        assert_eq!(reduced.len(), 1);
        assert!(reduced[0].is_constant());
    }

    #[test]
    fn interreduce_drops_zero_polynomials() {
        let ring = ring2();
        let zero = SparsePolynomial::zero();
        let x = SparsePolynomial::variable(0, &ring);
        let reduced = interreduce(vec![zero, x], &ring, None);
        // Zero dropped; left with `x`.
        assert_eq!(reduced.len(), 1);
        assert!(!reduced[0].is_zero());
    }
}
