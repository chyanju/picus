use super::*;
use crate::ff::field::PrimeField;
use num_bigint::BigUint;
use std::collections::HashMap;
use std::sync::Arc;

fn ring2() -> Arc<PolyRing> {
    PolyRing::new(
        PrimeField::new(BigUint::from(7u32)),
        vec!["x".into(), "y".into()],
        MonomialOrder::DegRevLex,
    )
}

fn mono(exps: Vec<u16>) -> Monomial {
    Monomial::from_exponents(exps)
}

// ────────── RowProv / Provenance ──────────

#[test]
fn rowprov_from_pair_seeds_pairs_only() {
    let p = RowProv::from_pair(7);
    assert_eq!(p.pairs.len(), 1);
    assert!(p.pairs.contains(&7));
    assert!(p.reducers.is_empty());
}

#[test]
fn rowprov_from_reducer_seeds_reducers_only() {
    let p = RowProv::from_reducer(3);
    assert!(p.pairs.is_empty());
    assert_eq!(p.reducers.len(), 1);
    assert!(p.reducers.contains(&3));
}

#[test]
fn rowprov_merge_unions_both_sets() {
    let mut a = RowProv::from_pair(1);
    a.reducers.insert(10);
    let mut b = RowProv::from_pair(2);
    b.reducers.insert(11);
    a.merge(&b);
    assert!(a.pairs.contains(&1) && a.pairs.contains(&2));
    assert!(a.reducers.contains(&10) && a.reducers.contains(&11));
}

// ────────── MonoKey ──────────

#[test]
fn mono_key_eq_compares_exponents() {
    let k1 = MonoKey::new(mono(vec![1, 0]), MonomialOrder::DegRevLex);
    let k2 = MonoKey::new(mono(vec![1, 0]), MonomialOrder::DegRevLex);
    let k3 = MonoKey::new(mono(vec![0, 1]), MonomialOrder::DegRevLex);
    assert_eq!(k1, k2);
    assert_ne!(k1, k3);
}

#[test]
fn mono_key_ord_uses_order() {
    // DegRevLex: deg first. (1,1) > (1,0).
    let bigger = MonoKey::new(mono(vec![1, 1]), MonomialOrder::DegRevLex);
    let smaller = MonoKey::new(mono(vec![1, 0]), MonomialOrder::DegRevLex);
    assert!(bigger > smaller);
    assert_eq!(
        bigger.partial_cmp(&smaller),
        Some(std::cmp::Ordering::Greater)
    );
}

#[test]
fn mono_key_hash_consistent_with_eq() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let k1 = MonoKey::new(mono(vec![1, 0]), MonomialOrder::DegRevLex);
    let k2 = MonoKey::new(mono(vec![1, 0]), MonomialOrder::Lex);
    // Equal by exponents → equal hashes (regardless of order field).
    let mut h1 = DefaultHasher::new();
    k1.hash(&mut h1);
    let mut h2 = DefaultHasher::new();
    k2.hash(&mut h2);
    assert_eq!(h1.finish(), h2.finish());
}

#[test]
fn mono_key_accessor_returns_monomial() {
    let m = mono(vec![2, 1]);
    let k = MonoKey::new(m.clone(), MonomialOrder::DegRevLex);
    assert_eq!(k.mono().exponents(), m.exponents());
}

// ────────── poly_to_sparse_row + sparse_row_to_poly round-trip ──────────

#[test]
fn row_round_trip_preserves_polynomial() {
    // p = 2·x·y + 3·x + 5 over GF(7).
    let ring = ring2();
    let p = DensePoly::from_terms(
        vec![
            (mono(vec![1, 1]), ring.field.from_int(2)),
            (mono(vec![1, 0]), ring.field.from_int(3)),
            (mono(vec![0, 0]), ring.field.from_int(5)),
        ],
        &ring,
    );
    // Build a monomial → column index matching p's monomials. Columns
    // assigned with LARGEST monomial first (DegRevLex sorts terms in
    // descending order, so iteration order gives ascending columns).
    let mut monomial_to_col: HashMap<MonoKey, usize> = HashMap::new();
    let mut col_to_monomial: Vec<Monomial> = Vec::new();
    for k in 0..p.num_terms() {
        let m = p.term(k, &ring).monomial();
        monomial_to_col.insert(MonoKey::new(m.clone(), ring.order), k);
        col_to_monomial.push(m);
    }

    let row = poly_to_sparse_row(&p, &monomial_to_col, &ring);
    // Row should have one (column, coeff) per term.
    assert_eq!(row.len(), p.num_terms());

    let q = sparse_row_to_poly(&row, &col_to_monomial, &ring);
    assert_eq!(q.num_terms(), p.num_terms());
}

#[test]
fn poly_to_sparse_row_skips_unmapped_monomials() {
    // Build a poly with a monomial NOT in the column index. The
    // converter silently skips it (used by symbolic preprocessing
    // to drop irrelevant rows).
    let ring = ring2();
    let p = DensePoly::from_terms(vec![(mono(vec![1, 0]), ring.field.from_int(2))], &ring);
    let monomial_to_col: HashMap<MonoKey, usize> = HashMap::new(); // empty
    let row = poly_to_sparse_row(&p, &monomial_to_col, &ring);
    assert!(row.is_empty());
}
