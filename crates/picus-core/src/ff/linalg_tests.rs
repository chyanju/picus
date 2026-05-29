use super::*;
use num_bigint::BigUint;
use std::collections::BTreeSet;

fn fe(field: &PrimeField, v: u64) -> FieldElem {
    field.from_biguint(&BigUint::from(v))
}

fn row(field: &PrimeField, entries: &[(usize, u64)]) -> Row {
    entries.iter().map(|&(c, v)| (c, fe(field, v))).collect()
}

/// Echelon of `[x+2y, x+3y]` over GF(7): second row reduces to `y`,
/// first stays monic in column 0.
#[test]
fn echelon_two_rows() {
    let field = PrimeField::new(BigUint::from(7u32));
    let mut rows = vec![
        row(&field, &[(0, 1), (1, 2)]),
        row(&field, &[(0, 1), (1, 3)]),
    ];
    echelonize_no_prov(&mut rows, &field, None);
    // Row 0: monic pivot at col 0.
    assert_eq!(rows[0][0].0, 0);
    assert_eq!(rows[0][0].1, fe(&field, 1));
    // Row 1: col-0 eliminated, monic pivot at col 1.
    assert_eq!(rows[1].len(), 1);
    assert_eq!(rows[1][0].0, 1);
    assert_eq!(rows[1][0].1, fe(&field, 1));
}

/// A linearly dependent row reduces to empty (rank deficiency).
#[test]
fn dependent_row_vanishes() {
    let field = PrimeField::new(BigUint::from(11u32));
    // r2 = 2 * r0, so after reduction r2 is empty.
    let mut rows = vec![
        row(&field, &[(0, 1), (2, 5)]),
        row(&field, &[(1, 1), (2, 3)]),
        row(&field, &[(0, 2), (2, 10)]),
    ];
    echelonize_no_prov(&mut rows, &field, None);
    assert!(rows[2].is_empty(), "dependent row must reduce to zero");
    assert_eq!(rows[0][0].0, 0);
    assert_eq!(rows[1][0].0, 1);
}

/// Provenance unions every pivot a row is reduced against.
#[test]
fn provenance_unions_reducers() {
    #[derive(Clone, Default)]
    struct Tag(BTreeSet<usize>);
    impl Provenance for Tag {
        fn merge(&mut self, other: &Self) {
            self.0.extend(other.0.iter().copied());
        }
    }
    let field = PrimeField::new(BigUint::from(13u32));
    let mut rows = vec![
        row(&field, &[(0, 1), (2, 1)]),
        row(&field, &[(1, 1), (2, 1)]),
        // r2 = col0 + col1. Reducing against r0 (pivot col0) leaves
        // col1 + col2; that lead (col1) then reduces against r1, so
        // r2 is combined with BOTH pivots.
        row(&field, &[(0, 1), (1, 1)]),
    ];
    let mut provs = vec![
        Tag([0].into_iter().collect()),
        Tag([1].into_iter().collect()),
        Tag([2].into_iter().collect()),
    ];
    echelonize(&mut rows, &mut provs, &field, None);
    // Row 2's provenance must include its own tag plus both pivots.
    assert!(provs[2].0.contains(&2));
    assert!(provs[2].0.contains(&0));
    assert!(provs[2].0.contains(&1));
}
