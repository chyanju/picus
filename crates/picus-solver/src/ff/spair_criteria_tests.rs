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

#[test]
fn gm_insert_f_criterion_replaces_with_coprime_at_equal_lcm() {
    // existing and new share lcm (1, 1). existing is non-coprime, new is
    // coprime ⇒ the Gebauer-Möller F-criterion replaces existing with the
    // coprime pair (and drops the rest implicitly: list length stays 1).
    let mut list = vec![make(vec![1, 1], 3, 1, false, (0, 1))];
    let new = make(vec![1, 1], 3, 2, true, (3, 4));
    gm_insert(&mut list, new);
    assert_eq!(list.len(), 1);
    // The surviving pair is the coprime newcomer (parents (3, 4)).
    assert_eq!(list[0].parents(), (3, 4));
    assert!(list[0].is_coprime());
}

#[test]
fn gm_insert_keeps_existing_at_equal_lcm_when_new_not_coprime() {
    // Same lcm, but the newcomer is NOT coprime: the F-criterion branch
    // is inert, the existing dominates, and the newcomer is dropped.
    let mut list = vec![make(vec![1, 1], 3, 1, false, (0, 1))];
    let new = make(vec![1, 1], 3, 2, false, (3, 4));
    gm_insert(&mut list, new);
    assert_eq!(list.len(), 1);
    // Existing kept unchanged.
    assert_eq!(list[0].parents(), (0, 1));
}

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
