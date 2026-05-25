//! F4 matrix encoding: row ↔ polynomial conversion and provenance.
//!
//! The sparse GF(p) row-echelon reducer itself lives in
//! [`picus_core::ff::linalg`] (shared with the linear and FGLM engines);
//! this module supplies the F4-specific pieces: encoding a [`DensePoly`]
//! to / from a sparse `(column, coefficient)` row, the [`MonoKey`]
//! column ordering, and the [`RowProv`] provenance carried through the
//! reduction.
//!
//! Columns are assigned with the LARGEST monomial at column 0; rows are
//! stored column-ASCENDING, so the first nonzero entry of a [`SparseRow`]
//! is always the row's leading term.

use std::collections::BTreeSet;

use crate::ff::field::FieldElem;
use crate::ff::linalg::{Provenance, Row};
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{PolyRing, DensePoly};

/// Row-provenance bookkeeping for the F4 echelon. Tracks which input
/// S-pairs and reducer basis elements have been linearly combined into a
/// given row; consumed by [`super::process_batch_with_workspace`] to
/// thread provenance into the F4 output.
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

impl Provenance for RowProv {
    fn merge(&mut self, other: &Self) {
        self.pairs.extend(other.pairs.iter().copied());
        self.reducers.extend(other.reducers.iter().copied());
    }
}

/// Sparse row over GF(p): `(column, coefficient)` pairs sorted by column
/// ASCENDING. Column 0 corresponds to the LARGEST monomial in the column
/// index, so the first nonzero entry is the row's LT. Alias of the shared
/// [`picus_core::ff::linalg::Row`].
pub(super) type SparseRow = Row;

/// Convert a polynomial to sparse row form (column-ascending). The
/// polynomial's terms are stored in monomial-DESCENDING order and
/// columns are assigned with the largest monomial at column 0, so
/// iterating terms in source order already yields ascending columns;
/// only a debug-mode sortedness check is run.
pub(super) fn poly_to_sparse_row(
    poly: &DensePoly,
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

/// Convert a sparse row back to a DensePoly.
pub(super) fn sparse_row_to_poly(
    row: &SparseRow,
    col_to_monomial: &[Monomial],
    ring: &PolyRing,
) -> DensePoly {
    let terms: Vec<(Monomial, FieldElem)> = row
        .iter()
        .map(|(c, v)| (col_to_monomial[*c].clone(), v.clone()))
        .collect();
    DensePoly::from_terms(terms, ring)
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
