//! Matrix-defined monomial orderings.
//!
//! A term ordering is given by an integer matrix `M`: monomials are
//! compared by their weight vectors `M·exp`, lexicographically by row
//! (the first differing row decides). Classical orders are special
//! cases — `Lex` is the identity matrix, `DegRevLex` is an all-ones
//! grading row over a reverse-lex block — and elimination / block /
//! weighted orders, which cannot be expressed as the fixed
//! [`MonomialOrder::Lex`](super::monomial::MonomialOrder)/`DegRevLex`
//! variants, are expressible here.
//!
//! Orders are heap-allocated (`rows: Vec<Vec<i64>>`), so they are not
//! carried inline in the `Copy` [`MonomialOrder`] enum. Instead a
//! [`MonomialOrder::Matrix`] variant holds a `u32` index into a
//! thread-local registry ([`intern`] / [`resolve`]), mirroring the
//! thread-local `RuntimeConfig` discipline. This keeps the enum one word
//! wide and `Copy`, so the comparison kernels in `monomial` /
//! `sparse_monomial` / `polynomial` gain a single additive match arm and
//! every by-value pass-through of `MonomialOrder` is unchanged.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::sync::Arc;

/// An integer matrix term ordering over `n_vars` indeterminates.
///
/// Rows are stored **sparsely** as `(column, value)` pairs, so comparison
/// costs `O(total nonzeros)` rather than `O(rows · n_vars)`. The built-in
/// orders are sparse (`degrevlex` is one dense degree row plus `n-1`
/// single-entry reverse-lex rows; `elim` adds one sparse marker row), so
/// a comparison is `O(n_vars)` — the same asymptotics as the classical
/// enum orders, which matters because matrix rings reach `2·n_wires`
/// indeterminates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixOrder {
    /// Weight rows as sparse `(column, value)` pairs (zeros omitted).
    /// Comparison reads them top to bottom and stops at the first row
    /// whose two weights differ.
    rows: Vec<Vec<(usize, i64)>>,
    n_vars: usize,
}

impl MatrixOrder {
    /// Build from explicit dense rows. Every row must have length
    /// `n_vars`; zero entries are dropped into the sparse representation.
    pub fn from_rows(rows: Vec<Vec<i64>>, n_vars: usize) -> Self {
        debug_assert!(
            rows.iter().all(|r| r.len() == n_vars),
            "every matrix-order row must have length n_vars"
        );
        let sparse = rows
            .into_iter()
            .map(|r| {
                r.into_iter()
                    .enumerate()
                    .filter(|&(_, v)| v != 0)
                    .collect::<Vec<(usize, i64)>>()
            })
            .collect();
        MatrixOrder { rows: sparse, n_vars }
    }

    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    pub fn n_rows(&self) -> usize {
        self.rows.len()
    }

    /// Pure lexicographic order: rows are the unit vectors `e_0..e_{n-1}`.
    /// Reproduces `MonomialOrder::Lex`.
    pub fn lex(n_vars: usize) -> Self {
        let rows = (0..n_vars).map(|i| vec![(i, 1i64)]).collect();
        MatrixOrder { rows, n_vars }
    }

    /// Degree-reverse-lexicographic order: an all-ones grading row over a
    /// reverse-lex block (`-e_{n-1}, -e_{n-2}, …, -e_1`). Reproduces
    /// `MonomialOrder::DegRevLex`.
    pub fn degrevlex(n_vars: usize) -> Self {
        let mut rows: Vec<Vec<(usize, i64)>> = Vec::with_capacity(n_vars);
        rows.push((0..n_vars).map(|i| (i, 1i64)).collect()); // total degree
        // Reverse-lex tiebreak: at equal degree, the monomial with the
        // smaller highest-index differing exponent is the larger — i.e.
        // negate the exponents from the last variable down to the second.
        for j in (1..n_vars).rev() {
            rows.push(vec![(j, -1i64)]);
        }
        MatrixOrder { rows, n_vars }
    }

    /// Elimination order for `elim_vars`: any monomial involving an
    /// eliminated variable is greater than any monomial that does not, so
    /// the basis drives those variables out of the leading terms first;
    /// the eliminant `I ∩ k[remaining]` falls out of the lower block. The
    /// grading row marks the eliminated variables, with `degrevlex` over
    /// all `n_vars` as the tiebreak.
    pub fn elim(elim_vars: &[usize], n_vars: usize) -> Self {
        let mut elim_row: Vec<(usize, i64)> = Vec::with_capacity(elim_vars.len());
        for &v in elim_vars {
            debug_assert!(v < n_vars, "elim var index out of range");
            elim_row.push((v, 1i64));
        }
        let mut rows = Vec::with_capacity(n_vars + 1);
        rows.push(elim_row);
        rows.extend(MatrixOrder::degrevlex(n_vars).rows);
        MatrixOrder { rows, n_vars }
    }

    /// Compare two dense exponent vectors under this order.
    #[inline]
    pub fn cmp_dense(&self, a: &[u16], b: &[u16]) -> Ordering {
        debug_assert_eq!(a.len(), self.n_vars);
        debug_assert_eq!(b.len(), self.n_vars);
        for row in &self.rows {
            // i64 accumulation: row entries are small (±1 for the built-in
            // orders) and exponents are u16, so the weight cannot overflow
            // i64 for any realistic ring width.
            let mut wa: i64 = 0;
            let mut wb: i64 = 0;
            for &(c, v) in row {
                wa += v * (a[c] as i64);
                wb += v * (b[c] as i64);
            }
            match wa.cmp(&wb) {
                Ordering::Equal => continue,
                o => return o,
            }
        }
        Ordering::Equal
    }

    /// Necessary admissibility condition: every single variable orders
    /// strictly above the constant monomial `1`. Built-in constructors
    /// satisfy this by construction; `from_rows` callers should check.
    pub fn is_admissible(&self) -> bool {
        let zero = vec![0u16; self.n_vars];
        for i in 0..self.n_vars {
            let mut unit = vec![0u16; self.n_vars];
            unit[i] = 1;
            if self.cmp_dense(&unit, &zero) != Ordering::Greater {
                return false;
            }
        }
        true
    }
}

thread_local! {
    /// Per-thread registry of interned matrix orders. A
    /// [`MonomialOrder::Matrix`] carries a `u32` index into this vector.
    /// Thread-local (not global) so it follows the same isolation as the
    /// runtime config; an index is only valid on the thread that interned
    /// it for as long as the registry lives.
    static MATRIX_REGISTRY: RefCell<Vec<Arc<MatrixOrder>>> =
        const { RefCell::new(Vec::new()) };
}

/// Intern a matrix order, returning its registry index for use as
/// `MonomialOrder::Matrix(idx)`.
pub fn intern(order: MatrixOrder) -> u32 {
    MATRIX_REGISTRY.with(|r| {
        let mut v = r.borrow_mut();
        let idx = v.len() as u32;
        v.push(Arc::new(order));
        idx
    })
}

/// Resolve a registry index back to its matrix order. Panics in debug if
/// the index was never interned on this thread.
pub fn resolve(idx: u32) -> Arc<MatrixOrder> {
    MATRIX_REGISTRY.with(|r| {
        let v = r.borrow();
        debug_assert!(
            (idx as usize) < v.len(),
            "matrix-order index {} not interned on this thread (len {})",
            idx,
            v.len()
        );
        v[idx as usize].clone()
    })
}

#[cfg(test)]
#[path = "matrix_order_tests.rs"]
mod tests;
