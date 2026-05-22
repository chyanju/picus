//! Sparse linear-algebra layer for F4.
//!
//! Provides the row-echelon reduction over GF(p) used by F4's
//! per-batch matrix step: row encoding/decoding between
//! [`Polynomial`] and sparse `(column, coefficient)` pairs, plus the
//! in-place echelon driver.
//!
//! Columns are assigned with the LARGEST monomial at column 0; rows
//! are stored column-ASCENDING, so the first nonzero entry of a
//! [`SparseRow`] is always the row's leading term.

use std::collections::BTreeSet;

use crate::ff::field::{FieldElem, PrimeField};
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{PolyRing, Polynomial};
use crate::timeout::CancelToken;

/// Row-provenance bookkeeping for sparse echelon. Tracks which input
/// S-pairs and reducer basis elements have been linearly combined
/// into a given row; consumed by [`super::process_batch_with_workspace`]
/// to thread provenance into the F4 output.
pub(super) struct RowProv {
    pub(super) pairs: BTreeSet<usize>,
    pub(super) reducers: BTreeSet<usize>,
}

impl RowProv {
    pub(super) fn from_pair(pair_idx: usize) -> Self {
        let mut p = BTreeSet::new();
        p.insert(pair_idx);
        RowProv { pairs: p, reducers: BTreeSet::new() }
    }

    pub(super) fn from_reducer(basis_idx: usize) -> Self {
        let mut r = BTreeSet::new();
        r.insert(basis_idx);
        RowProv { pairs: BTreeSet::new(), reducers: r }
    }
}

/// Sparse row over GF(p): list of (column, coefficient) pairs sorted
/// by column ASCENDING. Column 0 corresponds to the LARGEST monomial
/// in the column index, so the first nonzero entry is the row's LT.
pub(super) type SparseRow = Vec<(usize, FieldElem)>;
/// Convert a polynomial to sparse row form (column-ascending). The
/// polynomial's terms are stored in monomial-DESCENDING order and
/// columns are assigned with the largest monomial at column 0, so
/// iterating terms in source order already yields ascending columns;
/// only a debug-mode sortedness check is run.
pub(super) fn poly_to_sparse_row(
    poly: &Polynomial,
    monomial_to_col: &std::collections::HashMap<MonoKey, usize>,
    ring: &PolyRing,
) -> SparseRow {
    let mut row: SparseRow = Vec::with_capacity(poly.num_terms());
    for k in 0..poly.num_terms() {
        let term = poly.term(k, ring);
        let mono = term.monomial();
        let key = MonoKey::new(mono, ring.order);
        let col = match monomial_to_col.get(&key) {
            Some(&c) => c,
            None => continue,
        };
        row.push((col, term.coefficient().clone()));
    }
    debug_assert!(
        row.windows(2).all(|w| w[0].0 < w[1].0),
        "poly terms must produce columns in ascending order (largest \
         monomial → smallest column, by construction)"
    );
    row
}

/// Convert a sparse row back to a Polynomial.
pub(super) fn sparse_row_to_poly(
    row: &SparseRow,
    col_to_monomial: &[Monomial],
    ring: &PolyRing,
) -> Polynomial {
    let terms: Vec<(Monomial, FieldElem)> = row
        .iter()
        .map(|(c, v)| (col_to_monomial[*c].clone(), v.clone()))
        .collect();
    Polynomial::from_terms(terms, ring)
}

/// Sparse row echelon reduction over GF(p) with parallel provenance
/// tracking.
///
/// `rows` and `provs` are parallel arrays; `provs[i]` describes the
/// inputs (S-polys + reducers) whose contributions are linearly
/// combined to form `rows[i]` at any point during the reduction. Each
/// row-vs-pivot axpy (`row[i] -= scale * row[pivot]`) unions
/// `provs[pivot]` into `provs[i]`, so the final provenance of any row
/// is the complete set of contributing inputs.
pub(super) fn sparse_echelon(
    rows: &mut Vec<SparseRow>,
    provs: &mut [RowProv],
    field: &PrimeField,
    cancel: Option<&CancelToken>,
) {
    use std::collections::HashMap;
    debug_assert_eq!(rows.len(), provs.len());
    let mut pivots: HashMap<usize, usize> = HashMap::new();
    // Single scratch row threaded through every axpy in this
    // echelon pass; `mem::swap`-ped into / out of `rows[i]` per
    // pivot application.
    let mut scratch: SparseRow = Vec::new();

    for i in 0..rows.len() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return;
        }
        loop {
            if rows[i].is_empty() {
                break;
            }
            let lead_col = rows[i][0].0;
            let pivot_row = match pivots.get(&lead_col) {
                Some(&p) => p,
                None => break,
            };
            // `pivot_row < i` invariant: pivots are registered after
            // each outer iteration completes, so during this inner
            // loop every registered pivot points to a strictly-lower
            // row index. `split_at_mut(i)` then gives a non-aliasing
            // mutable borrow of the pivot (left half) and the current
            // row (right half[0]) simultaneously.
            debug_assert!(pivot_row < i, "pivot must be a previously processed row");
            let (left_rows, right_rows) = rows.split_at_mut(i);
            let (left_provs, right_provs) = provs.split_at_mut(i);
            let scale = right_rows[0][0].1.clone();
            // Move row[i] out (leaving an empty Vec in its place) so
            // we can consume its `FieldElem` coefficients into the
            // merge without cloning them. After the merge, swap
            // `scratch` back into row[i]; the empty placeholder ends
            // up in `scratch`, ready for the next axpy.
            let a = std::mem::take(&mut right_rows[0]);
            sparse_sub_scaled_consume_a(
                a,
                &left_rows[pivot_row],
                &scale,
                field,
                &mut scratch,
            );
            std::mem::swap(&mut right_rows[0], &mut scratch);
            // Union pivot prov into row[i]'s prov in-place; no
            // BTreeSet clone needed.
            let pivot_prov = &left_provs[pivot_row];
            right_provs[0]
                .pairs
                .extend(pivot_prov.pairs.iter().copied());
            right_provs[0]
                .reducers
                .extend(pivot_prov.reducers.iter().copied());
        }
        if rows[i].is_empty() {
            continue;
        }
        let lead_coeff = rows[i][0].1.clone();
        if !field.is_zero(&lead_coeff) {
            if let Some(inv) = field.inv(&lead_coeff) {
                for (_, c) in rows[i].iter_mut() {
                    *c = field.mul(c, &inv);
                }
            }
        }
        let lead_col = rows[i][0].0;
        pivots.insert(lead_col, i);
    }
}

/// Compute `a - scale * b` into `out`, **consuming** `a` so its
/// `FieldElem` coefficients are moved (not cloned) into the result
/// when they survive the merge. Both `a` and `b` are
/// column-ascending; the result is column-ascending. `out` is
/// cleared first and its existing allocation is reused.
///
/// Hot-path axpy inside [`sparse_echelon`]. The caller holds a single
/// scratch `SparseRow` and `mem::swap`s it into / out of `rows[i]`.
fn sparse_sub_scaled_consume_a(
    a: SparseRow,
    b: &SparseRow,
    scale: &FieldElem,
    field: &PrimeField,
    out: &mut SparseRow,
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

/// Wrapper around `Monomial` providing `Ord`/`Eq` keyed by a fixed
/// monomial order. Required because `Monomial` itself implements `Eq`
/// only on raw exponent equality (no order context).
#[derive(Clone, Debug)]
pub(super) struct MonoKey {
    mono: Monomial,
    order: MonomialOrder,
}

impl MonoKey {
    pub(super) fn new(mono: Monomial, order: MonomialOrder) -> Self {
        MonoKey { mono, order }
    }

    pub(super) fn mono(&self) -> &Monomial {
        &self.mono
    }
}

impl PartialEq for MonoKey {
    fn eq(&self, other: &Self) -> bool {
        self.mono.exponents() == other.mono.exponents()
    }
}
impl Eq for MonoKey {}
impl Ord for MonoKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.mono.cmp_with_order(&other.mono, self.order)
    }
}
impl PartialOrd for MonoKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl std::hash::Hash for MonoKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.mono.exponents().hash(state);
    }
}
