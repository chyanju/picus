use super::super::divmask::DivMaskScheme;
use super::super::monomial::Monomial;
use super::super::spair::SPair;
use super::*;

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
//
// gm_insert coverage lives in `buchberger/tests.rs::gm_insert_*` (5 cases:
// smaller_lcm_dominates_larger, larger_lcm_evicted_by_smaller,
// unrelated_lcms_both_kept, equal_lcm_prefers_coprime,
// equal_lcm_keeps_existing_otherwise) which exercises the same public
// `gm_insert` via the real `PolyRing` divmask path. The local-helper
// duplicates that used to live here are deleted.

// ────────── merge_sorted_descending: dst exhausts first ──────────

#[test]
fn merge_descending_drains_dst_then_extends_incoming() {
    // dst = [deg 3]; incoming = [deg 2, deg 1]. `dst` (the `a` iterator)
    // empties after one step, so the `(None, Some)` arm extends the
    // remaining incoming tail.
    let mut dst = vec![make(vec![3, 0], 3, 1, false, (0, 1))];
    let incoming = vec![
        make(vec![2, 0], 3, 2, false, (0, 2)),
        make(vec![1, 0], 3, 3, false, (1, 2)),
    ];
    merge_sorted_descending(&mut dst, incoming);
    assert_eq!(dst.len(), 3);
    assert_eq!(dst[0].lcm_deg, 3);
    assert_eq!(dst[1].lcm_deg, 2);
    assert_eq!(dst[2].lcm_deg, 1);
}

// ────────── b_criterion_kill ──────────
//
// b_criterion coverage lives in `buchberger/tests.rs::b_criterion_*`
// (5 cases: kills_when_all_three_conditions_hold, keeps_when_new_lt_does_not_divide_lcm,
// keeps_when_lcm_lt_j_new_equals_lcm, keeps_when_lcm_lt_i_new_equals_lcm,
// empty_queue_is_noop) which exercises the same public `b_criterion_kill`
// via real basis elements + ring divmask. The local-helper duplicate that
// used to live here is deleted.
