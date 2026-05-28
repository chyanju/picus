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
    /// True iff the parents' leading monomials are coprime. Used by the
    /// Gebauer-Möller F-criterion in [`gm_insert`]: among pairs sharing one
    /// `lcm`, if any is coprime then all may be discarded (the coprime
    /// pair's S-polynomial reduces to zero by the product criterion, which
    /// forces the others to as well). Engines that filter coprime pairs
    /// *before* [`gm_insert`] return `false` here, leaving that branch
    /// inert; engines that feed coprime pairs in rely on it for soundness.
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
///     replace `existing` with P — the Gebauer-Möller F-criterion (a
///     coprime pair among equal-`lcm` pairs lets all of them be dropped:
///     the coprime one falls to the product criterion, the rest follow).
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

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::divmask::DivMaskScheme;
    use super::super::monomial::Monomial;
    use super::super::spair::SPair;

    fn make(lcm_exps: Vec<u16>, sugar: u32, age: u64, coprime: bool, parents: (usize, usize)) -> SPair {
        let n = lcm_exps.len();
        let scheme = DivMaskScheme::build(n, 4);
        let lcm = Monomial::from_exponents(lcm_exps);
        let lcm_deg = lcm.total_degree();
        let lcm_divmask = scheme.compute(&lcm);
        SPair {
            i: parents.0,
            j: parents.1,
            sugar,
            lcm,
            lcm_divmask,
            lcm_deg,
            age,
            generation: 0,
            is_coprime: coprime,
        }
    }

    // ────────── merge_sorted_descending ──────────

    #[test]
    fn merge_descending_into_empty_takes_incoming() {
        let mut dst: Vec<SPair> = Vec::new();
        let a = make(vec![2, 0], 3, 1, false, (0, 1));
        let b = make(vec![1, 0], 3, 2, false, (0, 2));
        merge_sorted_descending(&mut dst, vec![a, b]);
        assert_eq!(dst.len(), 2);
        // Incoming was already descending → preserved.
        assert_eq!(dst[0].cmp_key().1, 2); // lcm_deg = 2 first
        assert_eq!(dst[1].cmp_key().1, 1); // then 1
    }

    #[test]
    fn merge_descending_empty_incoming_is_noop() {
        let mut dst = vec![make(vec![1, 0], 3, 1, false, (0, 1))];
        let dst_len_before = dst.len();
        merge_sorted_descending::<SPair>(&mut dst, vec![]);
        assert_eq!(dst.len(), dst_len_before);
    }

    #[test]
    fn merge_descending_preserves_descending_order() {
        // dst: [(deg 3), (deg 1)]; incoming: [(deg 2)]. Result must be
        // [(deg 3), (deg 2), (deg 1)].
        let mut dst = vec![
            make(vec![3, 0], 3, 1, false, (0, 1)),
            make(vec![1, 0], 3, 3, false, (1, 2)),
        ];
        let incoming = vec![make(vec![2, 0], 3, 2, false, (0, 2))];
        merge_sorted_descending(&mut dst, incoming);
        assert_eq!(dst.len(), 3);
        assert_eq!(dst[0].lcm_deg, 3);
        assert_eq!(dst[1].lcm_deg, 2);
        assert_eq!(dst[2].lcm_deg, 1);
    }

    // ────────── gm_insert ──────────

    #[test]
    fn gm_insert_into_empty_keeps_pair() {
        let mut list: Vec<SPair> = Vec::new();
        let p = make(vec![1, 1], 3, 1, false, (0, 1));
        gm_insert(&mut list, p);
        assert_eq!(list.len(), 1);
    }

    #[test]
    fn gm_insert_drops_dominated_pair() {
        // existing lcm = (1, 0); new lcm = (2, 0) — existing divides new → drop new.
        let mut list = vec![make(vec![1, 0], 3, 1, false, (0, 1))];
        let new = make(vec![2, 0], 3, 2, false, (0, 2));
        gm_insert(&mut list, new);
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].lcm.exponents(), &[1u16, 0u16]);
    }

    #[test]
    fn gm_insert_erases_dominated_existing() {
        // existing lcm = (2, 0); new lcm = (1, 0) — new divides existing → erase existing, keep new.
        let mut list = vec![make(vec![2, 0], 3, 1, false, (0, 1))];
        let new = make(vec![1, 0], 3, 2, false, (0, 2));
        gm_insert(&mut list, new);
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].lcm.exponents(), &[1u16, 0u16]);
    }

    // ────────── b_criterion_kill ──────────

    // The B-criterion needs a basis with leading terms. Build a minimal
    // wrapper.
    struct DummyBasis(Vec<Monomial>);
    impl LeadingTerms for DummyBasis {
        type Mono = Monomial;
        fn lt_at(&self, idx: usize) -> &Monomial {
            &self.0[idx]
        }
    }

    #[test]
    fn b_criterion_preserves_pairs_when_no_match() {
        // Basis has LT (0, 0) (constant 1). The new element's LT (1, 0)
        // doesn't divide any pair's lcm → nothing killed.
        let mut open = vec![make(vec![1, 1], 3, 1, false, (0, 1))];
        let basis = DummyBasis(vec![
            Monomial::from_exponents(vec![1, 0]), // basis[0].lt = (1,0)
            Monomial::from_exponents(vec![0, 1]), // basis[1].lt = (0,1)
        ]);
        let new_lt = Monomial::from_exponents(vec![5, 5]);
        let scheme = DivMaskScheme::build(2, 4);
        let new_lt_dm = scheme.compute(&new_lt);
        b_criterion_kill(&mut open, &new_lt, new_lt_dm, &basis);
        assert_eq!(open.len(), 1);
    }
}
