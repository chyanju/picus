//! Representation-agnostic S-pair pruning and queue maintenance for
//! Buchberger's algorithm.
//!
//! Three functions, generic over the monomial representation via
//! [`CriterionPair`] (the dense [`super::spair::SPair`] and the sparse
//! engine's S-pair both implement it), so the dense and sparse engines
//! share one copy:
//!
//! * [`gm_insert`] — Gebauer-Möller M-criterion. Inserts a new pair into a
//!   working list, dropping it if dominated by an existing pair and erasing
//!   pairs the new one dominates.
//! * [`b_criterion_kill`] — Buchberger B-criterion. Walks the open S-pair
//!   queue and erases pairs made redundant by a newly-added basis element's
//!   leading term.
//! * [`merge_sorted_descending`] — `O(n + m)` merge of two descending-sorted
//!   `Vec`s, preserving the descending invariant.
//!
//! The DivMask scheme differs by representation (dense threshold vs sparse
//! presence), but these functions only consult [`DivMask::divides_consistent_with`]
//! as a conservative prefilter before the full [`MonomialRepr::divides`]
//! check, so they are scheme-agnostic: each engine populates its pairs'
//! `lcm_divmask` its own way and the result is identical.

use picus_core::ff::divmask::DivMask;
use picus_core::ff::repr::MonomialRepr;

/// What the GM / B criteria need from an S-pair, independent of the
/// monomial representation.
pub trait CriterionPair {
    type Mono: MonomialRepr;
    /// `lcm(LT_i, LT_j)`.
    fn lcm(&self) -> &Self::Mono;
    /// Divisibility fingerprint of [`Self::lcm`].
    fn lcm_divmask(&self) -> DivMask;
    /// True iff the parents' leading monomials are coprime. On a same-`lcm`
    /// tie a coprime owner replaces a non-coprime one (the coprime pair is
    /// dropped downstream by the product criterion, so swapping it in
    /// eliminates the work). Engines whose coprime pairs never reach
    /// [`gm_insert`] return `false`, which makes that branch inert.
    fn is_coprime(&self) -> bool;
    /// Basis positions of the two parents `(i, j)`.
    fn parents(&self) -> (usize, usize);
    /// Priority-queue key `(sugar, lcm_deg, age)`; smaller is selected first.
    fn cmp_key(&self) -> (u32, u32, u64);
}

/// A basis exposing each element's leading monomial, for the B-criterion.
pub trait LeadingTerms {
    type Mono: MonomialRepr;
    fn lt_at(&self, idx: usize) -> &Self::Mono;
}

/// Gebauer-Möller M-criterion insertion.
///
/// A pair with a smaller `lcm` dominates pairs with larger `lcm`s:
/// `lcm(LT_a, LT_b)` dividing `lcm(LT_c, LT_d)` makes the `(c, d)` pair
/// redundant. So:
///   * If `LCM(existing) | LCM(P)`: existing dominates P, drop P. Special
///     case (LCMs equal): if `existing` is non-coprime and P is coprime,
///     replace `existing` with P.
///   * Else if `LCM(P) | LCM(existing)`: P dominates existing, erase existing.
///
/// On exit the list is left in arbitrary order; callers sort it before merging.
pub fn gm_insert<P: CriterionPair>(list: &mut Vec<P>, pair: P) {
    let mut to_insert = Some(pair);
    let mut dominated = false;
    let mut idx = 0;
    while idx < list.len() {
        let p_ref = match &to_insert {
            Some(p) => p,
            None => break,
        };
        // Existing dominates P iff LCM(existing) divides LCM(P).
        let existing_dominates = list[idx]
            .lcm_divmask()
            .divides_consistent_with(p_ref.lcm_divmask())
            && MonomialRepr::divides(list[idx].lcm(), p_ref.lcm());
        if existing_dominates {
            let same_lcm = p_ref.lcm() == list[idx].lcm();
            if same_lcm && !list[idx].is_coprime() && p_ref.is_coprime() {
                list[idx] = to_insert.take().unwrap();
            }
            dominated = true;
            break;
        }
        // Otherwise check if P strictly dominates existing.
        let p_dominates = p_ref
            .lcm_divmask()
            .divides_consistent_with(list[idx].lcm_divmask())
            && MonomialRepr::divides(p_ref.lcm(), list[idx].lcm());
        if p_dominates {
            // P strictly dominates (equality handled above). Erase existing
            // without advancing idx — swap_remove brings a not-yet-checked
            // element into position idx.
            list.swap_remove(idx);
            continue;
        }
        idx += 1;
    }
    if !dominated {
        if let Some(p) = to_insert {
            list.push(p);
        }
    }
}

/// Buchberger B-criterion. Walks `pairs` (the currently-pending S-pair
/// queue) and erases every pair that the newly-added basis element's
/// leading term `new_lt` makes redundant.
///
/// A pair `(i, j)` with cached `lcm = lcm(LT_i, LT_j)` is killed iff all
/// three conditions hold:
///   1. `new_lt | lcm` (DivMask prefilter, then full `divides` check),
///   2. `lcm(LT_j, new_lt) != lcm`,
///   3. `lcm(LT_i, new_lt) != lcm`.
///
/// Soundness depends on the substitute pairs `(i, new)` and `(j, new)` being
/// generated and discharged this round (or GM-dominated by some `(m, new)`
/// whose own obligation will be processed). A simpler chain criterion that
/// skipped conditions 2 and 3 would break that invariant.
///
/// The retain preserves the descending-sort invariant of `pairs`.
pub fn b_criterion_kill<P, B>(
    pairs: &mut Vec<P>,
    new_lt: &P::Mono,
    new_lt_divmask: DivMask,
    basis: &B,
) where
    P: CriterionPair,
    B: LeadingTerms<Mono = P::Mono>,
{
    pairs.retain(|p| {
        // Cheap reject: new LT must divide the pair's lcm to even consider it.
        if !new_lt_divmask.divides_consistent_with(p.lcm_divmask()) {
            return true;
        }
        if !MonomialRepr::divides(new_lt, p.lcm()) {
            return true;
        }
        // new LT divides p.lcm. Check the two non-equality conditions.
        let (i, j) = p.parents();
        if MonomialRepr::lcm(basis.lt_at(j), new_lt) == *p.lcm() {
            return true;
        }
        if MonomialRepr::lcm(basis.lt_at(i), new_lt) == *p.lcm() {
            return true;
        }
        // All three conditions hold ⇒ pair is killed.
        false
    });
}

/// Merge `incoming` (sorted descending by [`CriterionPair::cmp_key`]) into
/// `dst` (also sorted descending), preserving descending order. O(n + m).
pub fn merge_sorted_descending<P: CriterionPair>(dst: &mut Vec<P>, incoming: Vec<P>) {
    if incoming.is_empty() {
        return;
    }
    if dst.is_empty() {
        *dst = incoming;
        return;
    }
    let mut out: Vec<P> = Vec::with_capacity(dst.len() + incoming.len());
    let old = std::mem::take(dst);
    let mut a = old.into_iter().peekable();
    let mut b = incoming.into_iter().peekable();
    loop {
        match (a.peek(), b.peek()) {
            (Some(x), Some(y)) => {
                // descending: take the larger key first
                if x.cmp_key() > y.cmp_key() {
                    out.push(a.next().unwrap());
                } else {
                    out.push(b.next().unwrap());
                }
            }
            (Some(_), None) => {
                out.extend(a);
                break;
            }
            (None, Some(_)) => {
                out.extend(b);
                break;
            }
            (None, None) => break,
        }
    }
    *dst = out;
}
