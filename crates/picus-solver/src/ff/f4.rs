//! F4-lite: degree-batched matrix reduction (Faugère 1999).
//!
//! Where classical Buchberger processes one S-pair at a time, F4
//! processes a batch of same-sugar S-pairs together:
//!
//! 1. Build the S-polynomials for the whole batch.
//! 2. Symbolic preprocessing: any monomial appearing in some S-poly
//!    that is divisible by an active basis leading term is covered by
//!    adding a reducer row `(m / LT(b)) * b` to the matrix. Iterate
//!    until no uncovered divisible monomial remains.
//! 3. Build a sparse matrix whose rows are the S-polys plus the reducer
//!    rows, and whose columns are the union of all monomials appearing.
//! 4. Sparse row-echelon over GF(p).
//! 5. Each reduced S-poly row whose leading term is not a reducer LT
//!    (i.e. not divisible by any active basis LT) becomes a new GB
//!    generator.
//!
//! The per-pair geobucket merge is amortised into a single sparse
//! factorisation; shared monomials in the batch share reducer rows.
//!
//! Provenance tracking. Each output row's [`F4Output`] records the
//! batch-index of every input S-pair and the basis-index of every
//! reducer whose row was linearly combined (across `sparse_echelon`)
//! to produce it. `BuchbergerState::run_f4` threads those into the
//! observer protocol (`on_pair_reducers` + `on_new_poly`) so the
//! `GbTracer` UNSAT-core path remains sound when F4 is enabled.
//!
//! Implementation scope. No matrix reuse across batches; selection
//! strategy is lowest-sugar; layout is plain CSR-style rather than a
//! structured F4 layout. Symbolic preprocessing uses a `DivMask`
//! constant-time filter before the O(n_vars) `Monomial::divides`
//! check. The monomial → column index uses a `HashMap` after one
//! sort pass rather than per-insertion `BTreeMap` rebalancing.
//! `sparse_echelon` borrows pivot rows in-place via `split_at_mut`
//! to skip the per-axpy clone.
//!
//! Performance. Opt-in via `PICUS_USE_F4=1`. The
//! `tests/bench_perf.rs::bench_f4_vs_per_pair_large` micro-benchmark
//! (cyclic-N, dense degree-2 ideals) reports median ratios of
//! F4 / per-pair ≈ 1.01–1.15× depending on workload: dense-30 ties
//! (~1.01–1.04×); cyclic-5 ~1.07–1.14×. F4-lite does not beat
//! per-pair on any tested shape, so the default is per-pair.
//! Further improvements require structural work (cross-batch
//! matrix reuse, column-blocked sparse layout) tracked separately.

use std::collections::BTreeSet;
use std::sync::Arc;

use super::divmask::DivMask;
use super::field::{FieldElem, PrimeField};
use super::monomial::{Monomial, MonomialOrder};
use super::polynomial::{PolyRing, Polynomial};
use super::spair::SPair;
use crate::timeout::CancelToken;

/// Sparse row over GF(p): list of (column, coefficient) pairs sorted
/// by column ASCENDING. Column 0 corresponds to the LARGEST monomial
/// in the column index, so the first nonzero entry is the row's LT.
type SparseRow = Vec<(usize, FieldElem)>;

/// Information the F4 driver needs about each basis element.
///
/// Indexed in the same order as `BuchbergerState::basis` so SPair's
/// `i` / `j` indices remain valid. `active` distinguishes elements
/// usable as reducers (true) from non-strict-deactivated elements
/// kept around for S-pair generation history (false). `lt_divmask`
/// is the 128-bit divisibility fingerprint of `lt`, used as a
/// constant-time filter inside `symbolic_preprocess` before the
/// O(n_vars) `Monomial::divides` check.
pub struct F4BasisRef<'a> {
    pub poly: &'a Polynomial,
    pub lt: &'a Monomial,
    pub lt_divmask: DivMask,
    pub active: bool,
}

/// One generator produced by an F4 batch, paired with the set of input
/// pairs and reducer-basis indices whose rows contributed to it during
/// matrix reduction. Callers thread these into the `BuchbergerObserver`
/// callbacks (`on_pair_reducers` + `on_new_poly`) so the dependency
/// graph used by the UNSAT-core tracer stays accurate when the F4 path
/// runs in place of the per-pair geobucket reduction.
#[derive(Debug, Clone)]
pub struct F4Output {
    pub poly: Polynomial,
    /// Indices into the `batch[]` argument of [`process_batch`] —
    /// every pair whose S-polynomial row contributed to this output.
    pub from_pairs: Vec<usize>,
    /// Basis indices — every active basis element whose reducer row
    /// contributed to this output.
    pub from_reducers: Vec<usize>,
}

/// Per-row provenance carried through `sparse_echelon`.
#[derive(Clone, Default)]
struct RowProv {
    pairs: BTreeSet<usize>,
    reducers: BTreeSet<usize>,
}

impl RowProv {
    fn from_pair(pair_idx: usize) -> Self {
        let mut p = BTreeSet::new();
        p.insert(pair_idx);
        RowProv { pairs: p, reducers: BTreeSet::new() }
    }

    fn from_reducer(basis_idx: usize) -> Self {
        let mut r = BTreeSet::new();
        r.insert(basis_idx);
        RowProv { pairs: BTreeSet::new(), reducers: r }
    }
}

/// One F4 batch. Produces a list of new basis polynomials (already
/// monic but not yet inter-reduced; integration into the basis is the
/// caller's responsibility — same as `BuchbergerState::run` does
/// per-pair).
///
/// Returns an empty `Vec` if all S-polys reduced to zero (useless
/// reductions) or if cancel fired mid-way.
///
/// `basis` MUST contain only ACTIVE basis elements (the function
/// doesn't check `active` flags — caller filters first).
pub fn process_batch(
    batch: &[&SPair],
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
) -> Vec<F4Output> {
    if batch.is_empty() {
        return Vec::new();
    }
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 1: build S-polynomial for each pair, carrying the pair's
    // index in `batch[]` as the S-poly's provenance seed.
    // Each pair gives S = (lcm/lt_i) * f_i - (lc_i/lc_j) * (lcm/lt_j) * f_j.
    let mut spolys: Vec<Polynomial> = Vec::with_capacity(batch.len());
    let mut spoly_pair_idx: Vec<usize> = Vec::with_capacity(batch.len());
    for (pair_idx, pair) in batch.iter().enumerate() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return Vec::new();
        }
        let i = pair.i;
        let j = pair.j;
        if i >= basis.len() || j >= basis.len() {
            // The pair references a deactivated/missing basis index.
            continue;
        }
        let bi = &basis[i];
        let bj = &basis[j];
        let mul_i = pair.lcm.div(bi.lt);
        let mul_j = pair.lcm.div(bj.lt);
        let lc_i = bi.poly.leading_coefficient().expect("non-zero basis");
        let lc_j = bj.poly.leading_coefficient().expect("non-zero basis");
        let scale_j = match ring.field.div(lc_i, lc_j) {
            Some(s) => s,
            None => continue,
        };
        let one = ring.field.one();
        let part_i = bi.poly.mul_term(mul_i.exponents(), &one, ring);
        let neg_scale_j = ring.field.neg(&scale_j);
        let part_j = bj.poly.mul_term(mul_j.exponents(), &neg_scale_j, ring);
        let s_poly = part_i.add(&part_j, ring);
        if !s_poly.is_zero() {
            spolys.push(s_poly);
            spoly_pair_idx.push(pair_idx);
        }
    }
    if spolys.is_empty() {
        return Vec::new();
    }
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 2: symbolic preprocessing — add reducer rows to cover every
    // monomial divisible by some active basis LT.
    let (all_polys, n_spolys, reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(&spolys, basis, ring, cancel);
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 3: build the monomial → column index. Columns are sorted
    // by monomial DESCENDING (column 0 = largest monomial, i.e. the
    // potential LT of any row). A `HashSet` collects the unique
    // monomials in O(N) expected time, a single `sort_unstable_by`
    // produces the descending order, and the lookup map is built
    // by one linear pass.
    let mut all_monomials: std::collections::HashSet<MonoKey> =
        std::collections::HashSet::new();
    for poly in &all_polys {
        for k in 0..poly.num_terms() {
            let mono = poly.term(k, ring).monomial();
            all_monomials.insert(MonoKey::new(mono, ring.order));
        }
    }
    let mut sorted: Vec<MonoKey> = all_monomials.into_iter().collect();
    sorted.sort_unstable_by(|a, b| b.cmp(a)); // descending
    let mut monomial_to_col: std::collections::HashMap<MonoKey, usize> =
        std::collections::HashMap::with_capacity(sorted.len());
    let mut col_to_monomial: Vec<Monomial> = Vec::with_capacity(sorted.len());
    for k in sorted.into_iter() {
        let col = col_to_monomial.len();
        col_to_monomial.push(k.mono.clone());
        monomial_to_col.insert(k, col);
    }

    // Mark which columns correspond to reducer LTs (i.e. monomials
    // divisible by some active basis LT). After row reduction, any
    // S-poly residue whose LT column is in this set is redundant
    // (its LT is divisible by an existing basis element).
    let mut reducer_cols: std::collections::HashSet<usize> =
        std::collections::HashSet::with_capacity(reducer_lts.len());
    for lt in &reducer_lts {
        let key = MonoKey::new(lt.clone(), ring.order);
        if let Some(&c) = monomial_to_col.get(&key) {
            reducer_cols.insert(c);
        }
    }

    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 4: convert each polynomial to a sparse row (column-ascending).
    // Reducer rows come FIRST (in discovery order); S-poly rows come
    // LAST. The echelon pass establishes reducer LTs as pivots before
    // encountering S-polys, so each S-poly is reduced against the
    // reducers.
    //
    // `provs` runs parallel to `rows`. Reducer rows seed with their
    // contributing basis index; S-poly rows seed with their pair
    // index in `batch[]`. Provenance is unioned on each row-vs-pivot
    // axpy in `sparse_echelon`, so the final S-poly rows carry every
    // pair and reducer that participated in producing them.
    let n_reducers = all_polys.len() - n_spolys;
    let mut rows: Vec<SparseRow> = Vec::with_capacity(all_polys.len());
    let mut provs: Vec<RowProv> = Vec::with_capacity(all_polys.len());
    for (k, poly) in all_polys[n_spolys..].iter().enumerate() {
        rows.push(poly_to_sparse_row(poly, &monomial_to_col, ring));
        provs.push(RowProv::from_reducer(reducer_basis_idx[k]));
    }
    for (k, poly) in all_polys[..n_spolys].iter().enumerate() {
        rows.push(poly_to_sparse_row(poly, &monomial_to_col, ring));
        provs.push(RowProv::from_pair(spoly_pair_idx[k]));
    }

    // Step 5: sparse row-echelon reduce.
    sparse_echelon(&mut rows, &mut provs, &ring.field, cancel);

    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 6: extract new generators. The S-poly rows are now at
    // indices [n_reducers .. n_reducers + n_spolys].
    let mut out: Vec<F4Output> = Vec::new();
    for i in n_reducers..(n_reducers + n_spolys) {
        let row = &rows[i];
        if row.is_empty() {
            continue;
        }
        let lt_col = row[0].0;
        if reducer_cols.contains(&lt_col) {
            // After correct echelon a row whose LT lands on a reducer
            // pivot should already have been eliminated; defensive skip.
            continue;
        }
        let poly = sparse_row_to_poly(row, &col_to_monomial, ring);
        if poly.is_zero() {
            continue;
        }
        let monic = poly.make_monic(ring);
        let prov = &provs[i];
        out.push(F4Output {
            poly: monic,
            from_pairs: prov.pairs.iter().copied().collect(),
            from_reducers: prov.reducers.iter().copied().collect(),
        });
    }
    out
}

/// Symbolic preprocessing: given the S-polys, iteratively add reducer
/// rows for every monomial divisible by some active basis LT.
///
/// Returns:
/// - The combined polynomial list (S-polys first, then reducer rows).
/// - Number of S-polys (so caller can split back out).
/// - The set of monomials that became reducer LTs.
/// - For each reducer row (in discovery order, parallel to the
///   `all_polys[n_spolys..]` slice), the basis index it was built
///   from. Caller seeds row provenance from this.
fn symbolic_preprocess(
    spolys: &[Polynomial],
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
) -> (Vec<Polynomial>, usize, Vec<Monomial>, Vec<usize>) {
    let mut all_polys: Vec<Polynomial> = spolys.to_vec();
    let n_spolys = all_polys.len();
    let mut handled: std::collections::HashSet<MonoKey> = std::collections::HashSet::new();
    let mut reducer_lts: Vec<Monomial> = Vec::new();
    let mut reducer_basis_idx: Vec<usize> = Vec::new();

    let mut worklist: Vec<Monomial> = Vec::new();
    for poly in spolys {
        for k in 0..poly.num_terms() {
            let mono = poly.term(k, ring).monomial();
            let key = MonoKey::new(mono.clone(), ring.order);
            if handled.insert(key) {
                worklist.push(mono);
            }
        }
    }

    let mut idx = 0;
    while idx < worklist.len() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return (all_polys, n_spolys, reducer_lts, reducer_basis_idx);
        }
        let m = worklist[idx].clone();
        idx += 1;
        // Precompute the query monomial's divmask once per worklist
        // entry; every active basis check then short-circuits on a
        // constant-time bitmask comparison before the full
        // `Monomial::divides` (O(n_vars)) call.
        let m_mask = ring.divmask.compute(&m);
        let mut found: Option<usize> = None;
        for (bi, b) in basis.iter().enumerate() {
            if !b.active {
                continue;
            }
            if !b.lt_divmask.divides_consistent_with(m_mask) {
                continue;
            }
            if b.lt.divides(&m) {
                found = Some(bi);
                break;
            }
        }
        let bi = match found {
            Some(b) => b,
            None => continue,
        };
        let factor = m.div(basis[bi].lt);
        let one = ring.field.one();
        let reducer = basis[bi].poly.mul_term(factor.exponents(), &one, ring);
        if reducer.is_zero() {
            continue;
        }
        reducer_lts.push(m.clone());
        reducer_basis_idx.push(bi);
        for k in 0..reducer.num_terms() {
            let mono = reducer.term(k, ring).monomial();
            let key = MonoKey::new(mono.clone(), ring.order);
            if handled.insert(key) {
                worklist.push(mono);
            }
        }
        all_polys.push(reducer);
    }
    (all_polys, n_spolys, reducer_lts, reducer_basis_idx)
}

/// Convert a polynomial to sparse row form (column-ascending). The
/// polynomial's terms are stored in monomial-DESCENDING order and
/// columns are assigned with the largest monomial at column 0, so
/// iterating terms in source order already yields ascending columns;
/// only a debug-mode sortedness check is run.
fn poly_to_sparse_row(
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
fn sparse_row_to_poly(
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
fn sparse_echelon(
    rows: &mut Vec<SparseRow>,
    provs: &mut [RowProv],
    field: &PrimeField,
    cancel: Option<&CancelToken>,
) {
    use std::collections::HashMap;
    debug_assert_eq!(rows.len(), provs.len());
    let mut pivots: HashMap<usize, usize> = HashMap::new();

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
            // Avoid cloning the pivot row by using `split_at_mut` to
            // hold an immutable borrow on the pivot and a mutable
            // borrow on the current row at the same time. The
            // pivot_row is always less than `i` (pivots are
            // registered as `i` is processed), so a `split_at_mut`
            // at `i` puts the pivot in the left half and row[i] in
            // the right half.
            debug_assert!(pivot_row < i, "pivot must be a previously processed row");
            let (left_rows, right_rows) = rows.split_at_mut(i);
            let (left_provs, right_provs) = provs.split_at_mut(i);
            let scale = right_rows[0][0].1.clone();
            let new_row = sparse_sub_scaled(
                &right_rows[0],
                &left_rows[pivot_row],
                &scale,
                field,
            );
            right_rows[0] = new_row;
            // Union pivot prov into row[i]'s prov without cloning the
            // pivot's set: extend directly from `left_provs[pivot]`.
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

/// Compute `a - scale * b`, returning a new sparse row sorted by
/// column ascending. Both `a` and `b` are sorted ascending.
fn sparse_sub_scaled(
    a: &SparseRow,
    b: &SparseRow,
    scale: &FieldElem,
    field: &PrimeField,
) -> SparseRow {
    let mut out: SparseRow = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        let (ca, va) = (a[i].0, &a[i].1);
        let (cb, vb) = (b[j].0, &b[j].1);
        if ca < cb {
            out.push((ca, va.clone()));
            i += 1;
        } else if ca > cb {
            // a missing this column; result has -scale * vb
            let neg = field.neg(&field.mul(scale, vb));
            out.push((cb, neg));
            j += 1;
        } else {
            // both have column ca; result = va - scale * vb
            let prod = field.mul(scale, vb);
            let diff = field.sub(va, &prod);
            if !field.is_zero(&diff) {
                out.push((ca, diff));
            }
            i += 1;
            j += 1;
        }
    }
    while i < a.len() {
        out.push((a[i].0, a[i].1.clone()));
        i += 1;
    }
    while j < b.len() {
        let neg = field.neg(&field.mul(scale, &b[j].1));
        out.push((b[j].0, neg));
        j += 1;
    }
    out
}

/// Wrapper around `Monomial` providing `Ord`/`Eq` keyed by a fixed
/// monomial order. Required because `Monomial` itself implements `Eq`
/// only on raw exponent equality (no order context).
#[derive(Clone, Debug)]
struct MonoKey {
    mono: Monomial,
    order: MonomialOrder,
}

impl MonoKey {
    fn new(mono: Monomial, order: MonomialOrder) -> Self {
        MonoKey { mono, order }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::field::PrimeField;
    use crate::ff::polynomial::PolyRing;
    use num_bigint::BigUint;

    fn ring_mod7(n_vars: usize) -> Arc<PolyRing> {
        let f = PrimeField::new(BigUint::from(7u32));
        let names = (0..n_vars).map(|i| format!("x{}", i)).collect();
        PolyRing::new(f, names, MonomialOrder::DegRevLex)
    }

    fn x(idx: usize, ring: &Arc<PolyRing>) -> Polynomial {
        Polynomial::variable(idx, ring)
    }

    fn lt(p: &Polynomial, ring: &Arc<PolyRing>) -> Monomial {
        p.leading_monomial(ring).unwrap()
    }

    #[test]
    fn f4_minimal_two_variables() {
        // I = (x*y - 1, y^2 - x). The reduced GB in degrevlex is
        // (x*y - 1, y^2 - x, x^2 - y).
        let ring = ring_mod7(2);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        // f1 = x*y - 1
        let xy = x0.mul(&x1, &ring);
        let f1 = xy.sub(&Polynomial::constant(ring.field.one(), &ring), &ring);
        // f2 = y^2 - x
        let y2 = x1.mul(&x1, &ring);
        let f2 = y2.sub(&x0, &ring);
        let basis_polys = vec![f1.clone(), f2.clone()];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();

        // S(f1, f2): lcm(xy, y^2) = x*y^2.
        let lcm = lt(&f1, &ring).lcm(&lt(&f2, &ring));
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        let pair = SPair {
            i: 0,
            j: 1,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        };

        let new_polys = process_batch(&[&pair], &basis, &ring, None);
        assert!(!new_polys.is_empty(), "F4 batch produced no new polys");
        // The new poly's LT should be x^2 (the missing GB element).
        let np = &new_polys[0].poly;
        let np_lt = lt(np, &ring);
        // x^2 monomial: exponents [2, 0]
        assert_eq!(np_lt.exponents(), &[2, 0], "expected new LT x^2, got {:?}", np_lt.exponents());
        // Provenance: from_pairs must include the single input pair (index 0).
        assert_eq!(new_polys[0].from_pairs, vec![0]);
    }

    #[test]
    fn f4_matches_geobucket_on_random_pair_3vars() {
        // Cross-check: for the same S-pair, F4's batch result should
        // produce a polynomial whose normal-form-against-basis matches
        // the per-pair geobucket reduction. We pick a degree-2 system
        // in 3 vars and check both paths agree.
        let ring = ring_mod7(3);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let x2 = x(2, &ring);
        // f1 = x0*x1 - x2
        let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);
        // f2 = x1*x2 - x0
        let f2 = x1.mul(&x2, &ring).sub(&x0, &ring);
        let basis_polys = vec![f1.clone(), f2.clone()];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();

        // S(f1, f2): lcm(x0*x1, x1*x2) = x0*x1*x2.
        let lcm = lt(&f1, &ring).lcm(&lt(&f2, &ring));
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        let pair = SPair {
            i: 0,
            j: 1,
            sugar: lcm_deg,
            lcm: lcm.clone(),
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        };

        // F4 path
        let new_polys = process_batch(&[&pair], &basis, &ring, None);

        // Reference: build S-poly directly + reduce via reduce_by_refs.
        let mul1 = lcm.div(&lt(&f1, &ring));
        let mul2 = lcm.div(&lt(&f2, &ring));
        let one = ring.field.one();
        let part1 = f1.mul_term(mul1.exponents(), &one, &ring);
        let neg_one = ring.field.neg(&one);
        let part2 = f2.mul_term(mul2.exponents(), &neg_one, &ring);
        let s_poly = part1.add(&part2, &ring);
        let basis_refs: Vec<&Polynomial> = basis_polys.iter().collect();
        let reduced = s_poly.reduce_by_refs(&basis_refs, &ring);

        if reduced.is_zero() {
            assert!(new_polys.is_empty(), "F4 produced new poly but reference reduced to zero");
        } else {
            assert_eq!(new_polys.len(), 1);
            let f4_monic = &new_polys[0].poly;
            let ref_monic = reduced.make_monic(&ring);
            assert_eq!(
                f4_monic.num_terms(),
                ref_monic.num_terms(),
                "F4 and ref differ in num_terms",
            );
            assert_eq!(
                lt(f4_monic, &ring).exponents(),
                lt(&ref_monic, &ring).exponents(),
                "F4 and ref LT differ"
            );
        }
    }

    /// Build the ideal of all S-pairs on `basis_polys`, run BOTH F4 and
    /// per-pair `reduce_by_refs`, and check the two paths produce the
    /// SAME set of normal-form residues (modulo reordering, modulo
    /// trailing zeros).
    fn cross_check_all_pairs(basis_polys: Vec<Polynomial>, ring: &Arc<PolyRing>) {
        let basis_lts: Vec<Monomial> = basis_polys
            .iter()
            .map(|p| lt(p, ring))
            .collect();
        let n = basis_polys.len();
        let basis_refs: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();

        // Build ALL pairs (i, j) with i < j.
        let mut pairs: Vec<SPair> = Vec::new();
        for i in 0..n {
            for j in i + 1..n {
                let lcm = basis_lts[i].lcm(&basis_lts[j]);
                let lcm_dm = ring.divmask.compute(&lcm);
                let lcm_deg = lcm.total_degree();
                pairs.push(SPair {
                    i,
                    j,
                    sugar: lcm_deg,
                    lcm,
                    lcm_divmask: lcm_dm,
                    lcm_deg,
                    age: 0,
                    generation: 0,
                    is_coprime: false,
                });
            }
        }
        let pair_refs: Vec<&SPair> = pairs.iter().collect();

        // F4 path
        let f4_polys = process_batch(&pair_refs, &basis_refs, ring, None);

        // Reference: per-pair S-poly + reduce_by_refs.
        let basis_poly_refs: Vec<&Polynomial> = basis_polys.iter().collect();
        let mut ref_polys: Vec<Polynomial> = Vec::new();
        for pair in &pairs {
            let bi = &basis_polys[pair.i];
            let bj = &basis_polys[pair.j];
            let mul_i = pair.lcm.div(&basis_lts[pair.i]);
            let mul_j = pair.lcm.div(&basis_lts[pair.j]);
            let lc_i = bi.leading_coefficient().unwrap();
            let lc_j = bj.leading_coefficient().unwrap();
            let scale_j = ring.field.div(lc_i, lc_j).unwrap();
            let one = ring.field.one();
            let part_i = bi.mul_term(mul_i.exponents(), &one, ring);
            let part_j = bj.mul_term(mul_j.exponents(), &scale_j, ring);
            let s_poly = part_i.sub(&part_j, ring);
            let reduced = s_poly.reduce_by_refs(&basis_poly_refs, ring);
            if !reduced.is_zero() {
                ref_polys.push(reduced.make_monic(ring));
            }
        }

        // Compare LT sets — F4 may produce DIFFERENT (but ideal-equivalent)
        // representatives, but their LEADING TERMS w.r.t. the basis must
        // agree once we further reduce by the basis.
        //
        // Both sets, after reduction by the original basis, must:
        // (a) generate the same ideal extension (we don't check this
        //     directly; instead we check leading terms agree as a
        //     necessary condition).
        // (b) yield a non-empty set iff the other does.
        let f4_lts: std::collections::HashSet<Vec<u16>> = f4_polys
            .iter()
            .map(|o| {
                let r = o.poly.reduce_by_refs(&basis_poly_refs, ring);
                lt(&r, ring).exponents().to_vec()
            })
            .filter(|e| !e.is_empty() || true)
            .collect();
        let ref_lts: std::collections::HashSet<Vec<u16>> = ref_polys
            .iter()
            .map(|p| lt(p, ring).exponents().to_vec())
            .collect();
        assert_eq!(
            f4_lts, ref_lts,
            "F4 and reference disagree on new-generator leading terms.\nF4: {:?}\nref: {:?}",
            f4_lts, ref_lts
        );
    }

    #[test]
    fn f4_multipair_3vars_cyclic() {
        // Cyclic-3-style ideal: classic test.
        // f1 = x0 + x1 + x2
        // f2 = x0*x1 + x1*x2 + x2*x0
        // f3 = x0*x1*x2 - 1
        let ring = ring_mod7(3);
        let one = ring.field.one();
        let neg_one = ring.field.neg(&one);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let x2 = x(2, &ring);
        let f1 = x0.add(&x1.add(&x2, &ring), &ring);
        let f2 = x0.mul(&x1, &ring)
            .add(&x1.mul(&x2, &ring), &ring)
            .add(&x2.mul(&x0, &ring), &ring);
        let f3_part1 = x0.mul(&x1, &ring).mul(&x2, &ring);
        let f3 = f3_part1.add(&Polynomial::constant(neg_one, &ring), &ring);
        cross_check_all_pairs(vec![f1, f2, f3], &ring);
    }

    #[test]
    fn f4_multipair_3vars_overlapping_lts() {
        // Three polys with overlapping LTs to exercise reducer-chain
        // propagation in symbolic preprocessing.
        // f1 = x0^2 - x1
        // f2 = x0*x1 - x2
        // f3 = x1^2 - x0  (LT(f3) = x1^2 may need reducer chain)
        let ring = ring_mod7(3);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let x2 = x(2, &ring);
        let f1 = x0.mul(&x0, &ring).sub(&x1, &ring);
        let f2 = x0.mul(&x1, &ring).sub(&x2, &ring);
        let f3 = x1.mul(&x1, &ring).sub(&x0, &ring);
        cross_check_all_pairs(vec![f1, f2, f3], &ring);
    }

    #[test]
    fn f4_useless_reduction_yields_empty() {
        // I = (x, y). S(x, y) = y*x - x*y = 0 → useless reduction.
        let ring = ring_mod7(2);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let basis_polys = vec![x0.clone(), x1.clone()];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();

        let lcm = lt(&x0, &ring).lcm(&lt(&x1, &ring));
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        let pair = SPair {
            i: 0,
            j: 1,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: true,
        };
        let new_polys = process_batch(&[&pair], &basis, &ring, None);
        assert!(new_polys.is_empty(), "expected useless reduction, got {:?}", new_polys);
    }

    // ─── Provenance tracking ──────────────────────────────────────

    #[test]
    fn f4_prov_single_pair_no_reducers() {
        // S(x*y, x*z) over F_7: lcm = x*y*z; S-poly reduces against
        // nothing further; the output's provenance is exactly the one
        // input pair and no reducer.
        let ring = ring_mod7(3);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let x2 = x(2, &ring);
        let f1 = x0.mul(&x1, &ring); // x*y
        let f2 = x0.mul(&x2, &ring); // x*z
        let basis_polys = vec![f1.clone(), f2.clone()];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();
        let lcm = basis_lts[0].lcm(&basis_lts[1]);
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        let pair = SPair {
            i: 0,
            j: 1,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        };
        let new_polys = process_batch(&[&pair], &basis, &ring, None);
        // S(x*y, x*z) = z*(x*y) - y*(x*z) = 0 — useless reduction.
        // No outputs ⇒ no provenance to check, but the call must not
        // panic and must produce an empty Vec.
        assert!(new_polys.is_empty());
    }

    #[test]
    fn f4_prov_reducer_basis_index_recorded() {
        // System where the S-poly's tail needs a third basis element
        // as a reducer. After F4, the output's `from_reducers` must
        // name that basis index.
        //
        // basis[0] = x^2 + y           (LT = x^2)
        // basis[1] = x*y + z           (LT = x*y)
        // basis[2] = y                 (LT = y)
        //
        // S(basis[0], basis[1]) has tail terms involving `y`, which
        // basis[2] reduces. So the output's from_reducers must
        // include basis index 2.
        let ring = ring_mod7(3);
        let x0 = x(0, &ring); // x
        let x1 = x(1, &ring); // y
        let x2 = x(2, &ring); // z
        let f0 = x0.mul(&x0, &ring).add(&x1, &ring);   // x^2 + y
        let f1 = x0.mul(&x1, &ring).add(&x2, &ring);   // x*y + z
        let f2 = x1.clone();                            // y
        let basis_polys = vec![f0.clone(), f1.clone(), f2.clone()];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();
        let lcm = basis_lts[0].lcm(&basis_lts[1]);
        let lcm_dm = ring.divmask.compute(&lcm);
        let lcm_deg = lcm.total_degree();
        let pair = SPair {
            i: 0,
            j: 1,
            sugar: lcm_deg,
            lcm,
            lcm_divmask: lcm_dm,
            lcm_deg,
            age: 0,
            generation: 0,
            is_coprime: false,
        };
        let new_polys = process_batch(&[&pair], &basis, &ring, None);
        if let Some(out) = new_polys.first() {
            assert_eq!(out.from_pairs, vec![0],
                "the single pair's index must be in from_pairs");
            // basis[2] = y is the reducer pulled in during symbolic
            // preprocessing; its index must appear.
            assert!(out.from_reducers.contains(&2),
                "expected basis index 2 in from_reducers; got {:?}",
                out.from_reducers);
        }
    }

    #[test]
    fn f4_prov_multibatch_unions_pair_indices() {
        // Two pairs in one batch whose S-polys end up sharing
        // pivot columns during echelon. After elimination, the
        // surviving output rows must carry the union of contributing
        // pair indices.
        //
        // basis[0] = x^2 - y
        // basis[1] = x*y - 1
        // basis[2] = y^2 - x
        // pairs: (0,1), (0,2), (1,2).
        let ring = ring_mod7(3);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let f0 = x0.mul(&x0, &ring).sub(&x1, &ring);
        let f1 = x0.mul(&x1, &ring).sub(&Polynomial::constant(ring.field.one(), &ring), &ring);
        let f2 = x1.mul(&x1, &ring).sub(&x0, &ring);
        let basis_polys = vec![f0, f1, f2];
        let basis_lts: Vec<Monomial> = basis_polys.iter().map(|p| lt(p, &ring)).collect();
        let basis: Vec<F4BasisRef> = basis_polys
            .iter()
            .zip(basis_lts.iter())
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, lt_divmask: ring.divmask.compute(l), active: true })
            .collect();
        let mut pairs: Vec<SPair> = Vec::new();
        for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
            let lcm = basis_lts[i].lcm(&basis_lts[j]);
            let lcm_dm = ring.divmask.compute(&lcm);
            let lcm_deg = lcm.total_degree();
            pairs.push(SPair {
                i, j,
                sugar: lcm_deg,
                lcm,
                lcm_divmask: lcm_dm,
                lcm_deg,
                age: 0,
                generation: 0,
                is_coprime: false,
            });
        }
        let pair_refs: Vec<&SPair> = pairs.iter().collect();
        let outs = process_batch(&pair_refs, &basis, &ring, None);
        for out in &outs {
            assert!(!out.from_pairs.is_empty(),
                "every surviving output must name at least one input pair; got {:?}",
                out);
            for &pi in &out.from_pairs {
                assert!(pi < pairs.len(), "pair index out of range: {}", pi);
            }
        }
    }

    // ─── F4 + IncrementalGB push/pop integration ──────────────────

    /// `IncrementalGB::push`/`pop` must work with the F4 main-loop
    /// path enabled. The basis at the post-`pop` level must match
    /// the basis observed right after the pre-`push` extension.
    #[test]
    fn f4_incremental_push_pop_roundtrip() {
        use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
        let ring = ring_mod7(3);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);
        let x2 = x(2, &ring);

        let cfg = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: false,
            use_f4: true,
        };
        let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
        // Base level: f1, f2.
        let f1 = x0.mul(&x1, &ring).sub(&x2, &ring);
        let f2 = x1.mul(&x2, &ring).sub(&x0, &ring);
        igb.add_generators(vec![f1, f2]).expect("base add_generators");
        let base = igb.basis();
        assert!(!igb.is_trivial());

        // Push a checkpoint, extend with a third generator, then pop.
        igb.push();
        let f3 = x0.mul(&x0, &ring).sub(&x1, &ring);
        igb.add_generators(vec![f3]).expect("inner add_generators");
        let _inner = igb.basis();
        igb.pop();
        let restored = igb.basis();

        // The post-pop basis must match the pre-push basis.
        assert_eq!(
            restored.len(),
            base.len(),
            "F4 push/pop did not restore basis length"
        );
        for (a, b) in restored.iter().zip(base.iter()) {
            assert_eq!(
                lt(a, &ring).exponents(),
                lt(b, &ring).exponents(),
                "F4 push/pop basis LT mismatch"
            );
        }
    }

    /// F4 must not break when the trivial element is reached inside
    /// a `push`ed level. After `pop`, `is_trivial` must revert to
    /// the pre-push value.
    #[test]
    fn f4_incremental_pop_clears_trivial_state() {
        use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
        let ring = ring_mod7(2);
        let x0 = x(0, &ring);
        let x1 = x(1, &ring);

        let cfg = BuchbergerConfig {
            order: MonomialOrder::DegRevLex,
            cancel_token: None,
            abort_on_trivial: true,
            use_f4: true,
        };
        let mut igb = IncrementalGB::new(Arc::clone(&ring), cfg);
        igb.add_generators(vec![
            x0.mul(&x1, &ring).sub(
                &Polynomial::constant(ring.field.one(), &ring),
                &ring,
            ),
        ])
        .expect("base add");
        assert!(!igb.is_trivial());

        igb.push();
        // Add `x0` then `x1`: combined they force x0*x1 = 0,
        // contradicting x0*x1 = 1 ⇒ trivial.
        igb.add_generators(vec![x0.clone(), x1.clone()])
            .expect("inner add (trivial)");
        assert!(igb.is_trivial(), "inner extension should be trivial");

        igb.pop();
        assert!(!igb.is_trivial(), "pop must clear trivial state set inside push");
    }

    // ─── F4 vs per-pair cross-validation fuzz ─────────────────────

    /// Randomized cross-check: for a handful of small ideals, the
    /// F4-driven and per-pair-geobucket-driven incremental GB must
    /// produce bases whose leading-term sets agree.
    #[test]
    fn f4_vs_per_pair_random_cross_check() {
        use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
        use std::collections::HashSet;

        // Deterministic LCG for reproducibility; produces small
        // bivariate polynomials over F_7.
        fn lcg(seed: u64) -> impl FnMut() -> u64 {
            let mut s = seed;
            move || {
                s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                s
            }
        }

        for seed in 1u64..=12 {
            let ring = ring_mod7(2);
            let mut rng = lcg(seed);
            // Build 3 random bivariate polynomials, each of degree ≤ 2.
            let mut polys: Vec<Polynomial> = Vec::new();
            for _ in 0..3 {
                let one = ring.field.one();
                let x0 = x(0, &ring);
                let x1 = x(1, &ring);
                let xx = x0.mul(&x0, &ring);
                let yy = x1.mul(&x1, &ring);
                let xy = x0.mul(&x1, &ring);
                let const_one = Polynomial::constant(one.clone(), &ring);
                let mut acc = Polynomial::zero();
                for atom in [&xx, &xy, &yy, &x0, &x1, &const_one] {
                    let coeff = (rng() % 7) as u32;
                    if coeff == 0 { continue; }
                    let c = ring.field.from_int(coeff as i64);
                    let scaled = atom.mul(&Polynomial::constant(c, &ring), &ring);
                    acc = acc.add(&scaled, &ring);
                }
                if !acc.is_zero() {
                    polys.push(acc);
                }
            }
            if polys.len() < 2 {
                continue;
            }

            // Per-pair path. `abort_on_trivial: false` runs the
            // algorithm to quiescence even after a unit is found so
            // the comparison is against a fully-reduced GB.
            let cfg_pp = BuchbergerConfig {
                order: MonomialOrder::DegRevLex,
                cancel_token: None,
                abort_on_trivial: false,
                use_f4: false,
            };
            let mut igb_pp = IncrementalGB::new(Arc::clone(&ring), cfg_pp);
            let pp_trivial = igb_pp.add_generators(polys.clone()).expect("pp add");

            // F4 path.
            let cfg_f4 = BuchbergerConfig {
                order: MonomialOrder::DegRevLex,
                cancel_token: None,
                abort_on_trivial: false,
                use_f4: true,
            };
            let mut igb_f4 = IncrementalGB::new(Arc::clone(&ring), cfg_f4);
            let f4_trivial = igb_f4.add_generators(polys.clone()).expect("f4 add");

            // Both engines must agree on whether the ideal is the
            // whole ring (the only soundness-critical bit). If both
            // report trivial, the basis content is irrelevant — both
            // describe `R` regardless of which surviving polys
            // remain. If both report non-trivial, the LT sets must
            // match.
            assert_eq!(
                pp_trivial, f4_trivial,
                "F4 and per-pair disagree on triviality for seed={}: \
                 pp_trivial={} f4_trivial={}",
                seed, pp_trivial, f4_trivial
            );
            if !pp_trivial {
                let pp_lts: HashSet<Vec<u16>> = igb_pp
                    .basis()
                    .iter()
                    .map(|p| lt(p, &ring).exponents().to_vec())
                    .collect();
                let f4_lts: HashSet<Vec<u16>> = igb_f4
                    .basis()
                    .iter()
                    .map(|p| lt(p, &ring).exponents().to_vec())
                    .collect();
                assert_eq!(
                    pp_lts, f4_lts,
                    "F4 and per-pair LT sets differ for seed={}: \
                     pp={:?} f4={:?}",
                    seed, pp_lts, f4_lts
                );
            }
        }
    }
}
