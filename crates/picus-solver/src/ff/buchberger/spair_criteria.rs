//! S-pair pruning and queue maintenance for Buchberger's algorithm.
//!
//! Three pure functions operating on `Vec<SPair>`:
//!
//! * [`gm_insert`] — Gebauer-Möller M-criterion. Inserts a new pair into a
//!   working list, dropping it if dominated by an existing pair and erasing
//!   pairs the new one dominates.
//! * [`b_criterion_kill`] — Buchberger B-criterion. Walks the open S-pair
//!   queue and erases pairs made redundant by a newly-added basis element's
//!   leading term.
//! * [`merge_sorted_descending`] — `O(n + m)` merge of two descending-sorted
//!   `Vec<SPair>`s, preserving the descending invariant.

use super::super::divmask::DivMask;
use super::super::monomial::Monomial;
use super::super::spair::SPair;
use super::BasisElement;

/// Gebauer-Möller M-criterion insertion.
///
/// A pair with a smaller `lcm` dominates pairs with larger `lcm`s:
/// `lcm(LT_a, LT_b)` dividing `lcm(LT_c, LT_d)` makes the `(c, d)` pair
/// redundant. So:
///   * If `LCM(existing) | LCM(P)`: existing dominates P, drop P.
///     Special case (LCMs equal): if `existing` is non-coprime and P
///     is coprime, replace `existing` with P. Coprime pairs are dropped
///     by the product criterion downstream, so swapping in a coprime
///     owner for the same `lcm` eliminates the work entirely.
///   * Else if `LCM(P) | LCM(existing)`: P dominates existing, erase
///     existing.
///
/// On exit the list is left in arbitrary order; callers sort it before
/// merging.
pub(super) fn gm_insert(list: &mut Vec<SPair>, pair: SPair) {
    let mut to_insert = Some(pair);
    let mut dominated = false;
    let mut idx = 0;
    while idx < list.len() {
        let p_ref = match &to_insert {
            Some(p) => p,
            None => break,
        };
        let existing = &list[idx];
        // Existing dominates P iff LCM(existing) divides LCM(P).
        let existing_dominates =
            existing.lcm_divmask.divides_consistent_with(p_ref.lcm_divmask)
                && existing.lcm.divides(&p_ref.lcm);
        if existing_dominates {
            let same_lcm = p_ref.lcm == existing.lcm;
            if same_lcm && !existing.is_coprime && p_ref.is_coprime {
                list[idx] = to_insert.take().unwrap();
            }
            dominated = true;
            break;
        }
        // Otherwise check if P strictly dominates existing.
        let p_dominates =
            p_ref.lcm_divmask.divides_consistent_with(existing.lcm_divmask)
                && p_ref.lcm.divides(&existing.lcm);
        if p_dominates {
            // P strictly dominates (equality was handled above). Erase
            // existing without advancing idx — swap_remove brings a
            // not-yet-checked element into position idx.
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

/// Buchberger B-criterion. Walks `pairs` (the currently-pending
/// S-pair queue) and erases every pair that the newly-added basis
/// element's leading term `new_lt` makes redundant.
///
/// A pair `(i, j)` with cached `lcm = lcm(LT_i, LT_j)` is killed iff
/// all three conditions hold:
///   1. `new_lt | lcm` (DivMask prefilter, then full `Monomial` check),
///   2. `lcm(LT_j, new_lt) != lcm`,
///   3. `lcm(LT_i, new_lt) != lcm`.
///
/// Soundness depends on the substitute pairs `(i, new)` and `(j, new)`
/// being generated and discharged this round (or being GM-dominated by
/// some `(m, new)` whose own obligation will be processed). A simpler
/// "any third element's LT divides `lcm`" chain criterion that skipped
/// conditions 2 and 3 would break that invariant — this implementation
/// keeps all three.
///
/// The retain preserves the descending-sort invariant of `pairs`.
pub(super) fn b_criterion_kill(
    pairs: &mut Vec<SPair>,
    new_lt: &Monomial,
    new_lt_divmask: DivMask,
    basis: &[BasisElement],
) {
    pairs.retain(|p| {
        // Cheap reject: new LT must divide the pair's lcm to even consider
        // killing it.
        if !new_lt_divmask.divides_consistent_with(p.lcm_divmask) {
            return true;
        }
        if !new_lt.divides(&p.lcm) {
            return true;
        }
        // new LT divides p.lcm. Check the two non-equality conditions.
        let lcm_j_new = basis[p.j].lt.lcm(new_lt);
        if lcm_j_new == p.lcm {
            return true;
        }
        let lcm_i_new = basis[p.i].lt.lcm(new_lt);
        if lcm_i_new == p.lcm {
            return true;
        }
        // All three conditions hold ⇒ pair is killed.
        false
    });
}

/// Merge `incoming` (sorted descending) into `dst` (also sorted descending),
/// preserving descending order. O(n + m).
pub(super) fn merge_sorted_descending(dst: &mut Vec<SPair>, incoming: Vec<SPair>) {
    if incoming.is_empty() {
        return;
    }
    if dst.is_empty() {
        *dst = incoming;
        return;
    }
    let mut out: Vec<SPair> = Vec::with_capacity(dst.len() + incoming.len());
    let old = std::mem::take(dst);
    let mut a = old.into_iter().peekable();
    let mut b = incoming.into_iter().peekable();
    loop {
        match (a.peek(), b.peek()) {
            (Some(x), Some(y)) => {
                // descending: take the larger first
                if x.cmp(y) == std::cmp::Ordering::Greater {
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
