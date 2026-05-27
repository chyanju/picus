//! Sparse linear algebra over GF(p): in-place row echelon reduction.
//!
//! Shared substrate for the engines in `picus-solver` that all reduce
//! sparse GF(p) systems — F4's per-batch Macaulay matrix, linear
//! pre-elimination, and FGLM order conversion. Rows are sparse
//! `(column, coefficient)` lists; the reducer is generic over a
//! [`Provenance`] type so a caller that needs dependency / UNSAT-core
//! tracking can thread its own bookkeeping through the row combinations,
//! while a caller that does not pays nothing (the no-op `()` impl).
//!
//! Rows are stored column-ASCENDING, so the first nonzero entry of a
//! [`Row`] is its leading (pivot) column. Callers that derive columns
//! from a monomial order must assign the LARGEST monomial to column 0
//! for the leading entry to be the leading term.

use crate::ff::field::{FieldElem, PrimeField};
use crate::timeout::CancelToken;

/// Sparse row over GF(p): `(column, coefficient)` pairs sorted by column
/// ASCENDING. The first entry (if any) is the row's pivot.
pub type Row = Vec<(usize, FieldElem)>;

/// Per-row bookkeeping threaded through the reduction. Each time a row
/// is reduced by a pivot row, the pivot's provenance is `merge`d into
/// the row's, so the final provenance of any row is the union over every
/// input that contributed to it.
///
/// The no-op `()` impl is for callers that don't track provenance.
pub trait Provenance {
    fn merge(&mut self, other: &Self);
}

impl Provenance for () {
    #[inline]
    fn merge(&mut self, _other: &Self) {}
}

/// In-place sparse row echelon reduction over GF(p), tracking provenance.
///
/// `rows` and `provs` are parallel; `provs[i]` accumulates the inputs
/// whose contributions are linearly combined into `rows[i]`. Each
/// row-vs-pivot axpy (`rows[i] -= scale * rows[pivot]`) merges
/// `provs[pivot]` into `provs[i]`. On return each surviving row is monic
/// (leading coefficient 1) with a distinct pivot column; rows that
/// reduced to zero are left empty.
pub fn echelonize<P: Provenance>(
    rows: &mut [Row],
    provs: &mut [P],
    field: &PrimeField,
    cancel: Option<&CancelToken>,
) {
    use std::collections::HashMap;
    debug_assert_eq!(rows.len(), provs.len());
    // pivot column → index of the (already-processed) row owning it.
    let mut pivots: HashMap<usize, usize> = HashMap::new();
    // Single scratch row threaded through every axpy in this pass;
    // `mem::swap`-ped into / out of `rows[i]` per pivot application so no
    // coefficient is cloned.
    let mut scratch: Row = Vec::new();

    for i in 0..rows.len() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return;
        }
        // Inner-loop cancel cadence: a wide row can chain dozens of
        // pivot applications, each O(row length). The token is checked
        // once per `CANCEL_PERIOD` pivots so a cancelled request returns
        // within bounded extra work.
        const CANCEL_PERIOD: u32 = 16;
        let mut inner_steps: u32 = 0;
        loop {
            if rows[i].is_empty() {
                break;
            }
            inner_steps = inner_steps.wrapping_add(1);
            if inner_steps % CANCEL_PERIOD == 0
                && cancel.map(|c| c.is_cancelled()).unwrap_or(false)
            {
                return;
            }
            let lead_col = rows[i][0].0;
            let pivot_row = match pivots.get(&lead_col) {
                Some(&p) => p,
                None => break,
            };
            // `pivot_row < i` invariant: pivots are registered only after
            // an outer iteration completes, so every registered pivot
            // points to a strictly-lower row index. `split_at_mut(i)`
            // then yields a non-aliasing mutable borrow of the pivot
            // (left half) and the current row (right half[0]).
            debug_assert!(pivot_row < i, "pivot must be a previously processed row");
            let (left_rows, right_rows) = rows.split_at_mut(i);
            let (left_provs, right_provs) = provs.split_at_mut(i);
            let scale = right_rows[0][0].1.clone();
            // Move row[i] out (leaving an empty Vec) so its coefficients
            // are consumed into the merge without cloning; swap `scratch`
            // back in afterwards, leaving the empty placeholder in
            // `scratch` for the next axpy.
            let a = std::mem::take(&mut right_rows[0]);
            sub_scaled_consume_a(a, &left_rows[pivot_row], &scale, field, &mut scratch);
            std::mem::swap(&mut right_rows[0], &mut scratch);
            right_provs[0].merge(&left_provs[pivot_row]);
        }
        if rows[i].is_empty() {
            continue;
        }
        let lead_coeff = rows[i][0].1.clone();
        if !field.is_zero(&lead_coeff) {
            let inv = field
                .inv(&lead_coeff)
                .expect("prime field: a nonzero element is invertible");
            for (_, c) in rows[i].iter_mut() {
                *c = field.mul(c, &inv);
            }
        }
        let lead_col = rows[i][0].0;
        pivots.insert(lead_col, i);
    }
}

/// Convenience: echelonize without provenance tracking.
pub fn echelonize_no_prov(rows: &mut [Row], field: &PrimeField, cancel: Option<&CancelToken>) {
    let mut provs = vec![(); rows.len()];
    echelonize(rows, &mut provs, field, cancel);
}

/// Compute `a - scale * b` into `out`, **consuming** `a` so its
/// coefficients move (not clone) into the result when they survive the
/// merge. Both `a` and `b` are column-ascending; the result is
/// column-ascending. `out` is cleared first; its allocation is reused.
fn sub_scaled_consume_a(
    a: Row,
    b: &Row,
    scale: &FieldElem,
    field: &PrimeField,
    out: &mut Row,
) {
    out.clear();
    out.reserve(a.len() + b.len());
    let mut a_iter = a.into_iter();
    let mut a_cur: Option<(usize, FieldElem)> = a_iter.next();
    let mut j = 0usize;
    while a_cur.is_some() && j < b.len() {
        let ca = a_cur.as_ref().unwrap().0;
        let cb = b[j].0;
        if ca < cb {
            out.push(a_cur.take().unwrap());
            a_cur = a_iter.next();
        } else if ca > cb {
            let neg = field.neg(&field.mul(scale, &b[j].1));
            out.push((cb, neg));
            j += 1;
        } else {
            let (_, va) = a_cur.take().unwrap();
            let prod = field.mul(scale, &b[j].1);
            let diff = field.sub(&va, &prod);
            if !field.is_zero(&diff) {
                out.push((ca, diff));
            }
            j += 1;
            a_cur = a_iter.next();
        }
    }
    if let Some(elem) = a_cur {
        out.push(elem);
    }
    for elem in a_iter {
        out.push(elem);
    }
    while j < b.len() {
        let neg = field.neg(&field.mul(scale, &b[j].1));
        out.push((b[j].0, neg));
        j += 1;
    }
}

#[cfg(test)]
mod tests {
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
        let mut rows = vec![row(&field, &[(0, 1), (1, 2)]), row(&field, &[(0, 1), (1, 3)])];
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
}
