//! F4-lite: degree-batched matrix reduction (Faugère 1999).
//!
//! Algorithm. Per batch of same-sugar S-pairs:
//!
//! 1. Build the S-polynomials for the batch.
//! 2. Symbolic preprocessing: for every monomial appearing in some
//!    S-poly that is divisible by an active basis leading term, add
//!    a reducer row `(m / LT(b)) * b` to the matrix; iterate until
//!    no uncovered divisible monomial remains.
//! 3. Build a sparse matrix over the union of all monomials.
//! 4. Sparse row-echelon over GF(p).
//! 5. Each reduced S-poly row whose LT is not divisible by any
//!    active basis LT becomes a new generator.
//!
//! Per-pair selection is lowest-sugar. The sparse row layout is CSR.
//! Batches with `len < F4_MIN_BATCH` route to the per-pair geobucket
//! path in `BuchbergerState::run_f4`.
//!
//! Provenance. Each [`F4Output`] records the batch-index of every
//! input S-pair and the basis-index of every reducer whose row was
//! linearly combined to produce it (`RowProv` is unioned per
//! `sparse_echelon` axpy). `BuchbergerState::run_f4` threads these
//! into `on_pair_reducers` + `on_new_poly` so the `GbTracer` UNSAT-
//! core path stays sound under F4.
//!
//! Optimisations.
//!
//! * Symbolic preprocessing applies the `DivMask` constant-time
//!   filter before the O(n_vars) `Monomial::divides` check.
//! * The monomial → column index uses a `HashMap` built from a
//!   single sort pass over the unique monomial set.
//! * `sparse_echelon` borrows pivot rows in place via `split_at_mut`
//!   and threads one `SparseRow` scratch buffer through every axpy
//!   via [`sparse_sub_scaled_consume_a`], which moves `FieldElem`
//!   coefficients into the merge instead of cloning them.
//! * [`F4Workspace`] caches `monomial → (basis_idx, reducer_poly)`
//!   across batches, invalidating entries whose `basis_idx` becomes
//!   inactive. The same workspace owns the per-batch scratch buffers
//!   (`handled` / `worklist` in symbolic preprocessing, the
//!   monomial-set / column-map / reducer-column index built before
//!   sparse-row encoding); each is `mem::take`d into a local at
//!   call entry and assigned back at exit so allocator capacity
//!   persists across batches in the same Buchberger run.
//!
//! Performance. Opt-in via `PICUS_USE_F4=1`. F4 / per-pair median
//! ratios at `F4_MIN_BATCH = 12`
//! (`tests/bench_perf.rs::bench_f4_vs_per_pair_large` +
//! `bench_f4_non_cyclic_workloads`):
//!
//! | workload | ratio |
//! |---|---|
//! | cyclic-4 | 0.82–0.92× |
//! | cyclic-5 | 0.91–1.12× |
//! | cyclic-6 | 1.06–1.20× |
//! | dense-10/20/30 | 0.96–1.02× |
//! | katsura-3 | 0.77–0.88× |
//! | katsura-4 | 0.92–1.02× |
//! | diffuse-4vars | 0.92–1.15× |
//!
//! Default is per-pair (`use_f4_default()` returns `true` iff
//! `PICUS_USE_F4=1`). `PICUS_GB_STATS=1` emits per-run cache hits /
//! misses / stales and the F4 batch-size distribution.
//!
//! [`super::hilbert::hilbert_numerator`] is available as a building
//! block for monomial-ideal heuristics. F4 batch dispatch does not
//! gate on it: the Gebauer–Möller M-criterion in `gm_insert` already
//! collapses same-LCM pairs before they reach the batch, leaving a
//! Hilbert-based gate `Ω(batch.len())` on every surviving input.

mod matrix;

use std::sync::Arc;

use super::divmask::DivMask;
use super::monomial::Monomial;
use super::polynomial::{PolyRing, DensePoly};
use super::spair::SPair;
use crate::timeout::CancelToken;
use matrix::{poly_to_sparse_row, sparse_echelon, sparse_row_to_poly, MonoKey, RowProv, SparseRow};


/// View of a basis element for F4 consumption.
///
/// Indexed parallel to `BuchbergerState::basis` so `SPair::{i, j}`
/// remain valid. `active = true` means the element is usable as a
/// reducer; `false` means non-strict-deactivated (retained for
/// S-pair generation but skipped during symbolic preprocessing).
/// `lt_divmask` is the 128-bit divisibility fingerprint of `lt`,
/// used by `symbolic_preprocess` as a constant-time filter before
/// the O(n_vars) `Monomial::divides` check.
pub struct F4BasisRef<'a> {
    pub poly: &'a DensePoly,
    pub lt: &'a Monomial,
    pub lt_divmask: DivMask,
    pub active: bool,
}

/// One generator produced by an F4 batch, with the input pairs and
/// reducer-basis indices whose rows contributed to it during matrix
/// reduction. `BuchbergerState::run_f4` forwards `from_pairs` /
/// `from_reducers` into `BuchbergerObserver::on_pair_reducers` and
/// `on_new_poly` so the `GbTracer` UNSAT-core dependency graph
/// stays accurate under F4.
#[derive(Debug, Clone)]
pub struct F4Output {
    pub poly: DensePoly,
    /// Indices into the `batch[]` argument of [`process_batch`] —
    /// every pair whose S-polynomial row contributed to this output.
    pub from_pairs: Vec<usize>,
    /// Basis indices — every active basis element whose reducer row
    /// contributed to this output.
    pub from_reducers: Vec<usize>,
}

/// Cross-batch state kept by [`BuchbergerState::run_f4`] across
/// consecutive [`process_batch_with_workspace`] calls in a single
/// Buchberger run.
///
/// Holds two kinds of state:
///
/// 1. A per-monomial reducer cache mapping a monomial to
///    `(basis_idx, reducer_poly)`, where `reducer_poly` equals
///    `basis[basis_idx].poly * (monomial / LT(basis[basis_idx]))`.
///    Symbolic preprocessing iterates active basis elements in index
///    order and picks the lowest-index match, so the chosen index is
///    stable as long as `basis[basis_idx].active` stays true and the
///    basis is append-only (newer additions can never displace an
///    existing match). The cache verifies the active flag before
///    reuse and falls through to recomputation if the cached element
///    has been deactivated.
/// 2. Per-batch scratch collections (`handled_scratch`,
///    `worklist_scratch`, the monomial-set / sorted-list / column-map
///    / reducer-LT-column index, and the `reducer_lts` /
///    `reducer_basis_idx` lists used during symbolic preprocessing).
///    Each is `mem::take`-d into a local at function entry and
///    returned at the end of the call, so the allocator-owned
///    capacity is reused across batches even though the logical
///    contents are not.
///
/// `F4Workspace::new()` returns an empty workspace. Passing a fresh
/// workspace on every call disables both the cache and the scratch
/// reuse — output is unchanged, allocator traffic increases.
#[derive(Default)]
pub struct F4Workspace {
    /// `m -> (basis_idx, reducer_poly)`. The cache is keyed only by
    /// the monomial because the basis-element choice is uniquely
    /// determined by `m` and the current active set.
    reducer_cache: std::collections::HashMap<MonoKey, (usize, DensePoly)>,
    /// Diagnostic counters; updated by `process_batch_with_workspace`.
    pub stats: F4WorkspaceStats,
    // Per-batch scratch collections. `process_batch_with_workspace`
    // and `symbolic_preprocess` `mem::take` each into a local at
    // function entry and assign it back at exit. The allocator-
    // owned capacity carries over between batches; the logical
    // contents do not.
    handled_scratch: std::collections::HashSet<MonoKey>,
    worklist_scratch: Vec<Monomial>,
    reducer_lts_scratch: Vec<Monomial>,
    reducer_basis_idx_scratch: Vec<usize>,
    all_monomials_scratch: std::collections::HashSet<MonoKey>,
    monomial_sorted_scratch: Vec<MonoKey>,
    monomial_to_col_scratch: std::collections::HashMap<MonoKey, usize>,
    col_to_monomial_scratch: Vec<Monomial>,
    reducer_cols_scratch: std::collections::HashSet<usize>,
}

/// Cache-hit / miss statistics for diagnostic and benchmark use.
#[derive(Default, Debug, Clone, Copy)]
pub struct F4WorkspaceStats {
    pub reducer_hits: u64,
    pub reducer_misses: u64,
    pub reducer_stale: u64,
}

impl F4Workspace {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Process one F4 batch. Returns the new basis generators produced
/// by the batch (already monic, not inter-reduced — integration is
/// the caller's responsibility).
///
/// Returns an empty `Vec` when every S-polynomial reduces to zero or
/// when `cancel` fires mid-call.
///
/// `basis` must contain only active basis elements; the function
/// does not check `active` flags.
pub fn process_batch(
    batch: &[&SPair],
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
) -> Vec<F4Output> {
    let mut workspace = F4Workspace::new();
    process_batch_with_workspace(batch, basis, ring, cancel, &mut workspace)
}

/// Workspace-threaded variant of [`process_batch`]. Caches the
/// reducer-row computation across calls in
/// `workspace.reducer_cache`; output matches [`process_batch`]
/// exactly for any input.
pub fn process_batch_with_workspace(
    batch: &[&SPair],
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
    workspace: &mut F4Workspace,
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
    let mut spolys: Vec<DensePoly> = Vec::with_capacity(batch.len());
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
    // monomial divisible by some active basis LT. The S-polynomial
    // vector is moved into `symbolic_preprocess` so it can be reused
    // as the prefix of `all_polys` without a per-batch clone.
    let (all_polys, n_spolys, reducer_lts, reducer_basis_idx) =
        symbolic_preprocess(spolys, basis, ring, cancel, workspace);
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 3: build the monomial → column index. Columns are sorted
    // by monomial DESCENDING (column 0 = largest monomial, i.e. the
    // potential LT of any row). A `HashSet` collects the unique
    // monomials in O(N) expected time, a single `sort_unstable_by`
    // produces the descending order, and the lookup map is built
    // by one linear pass.
    //
    // Scratch reuse: take the workspace's owned scratch collections
    // into locals via `mem::take`, then move them back into the
    // workspace at the end of this call. Their allocator-owned
    // capacity carries across batches even though the logical
    // contents do not.
    let mut all_monomials = std::mem::take(&mut workspace.all_monomials_scratch);
    all_monomials.clear();
    for poly in &all_polys {
        for k in 0..poly.num_terms() {
            let mono = poly.term(k, ring).monomial();
            all_monomials.insert(MonoKey::new(mono, ring.order));
        }
    }
    let mut sorted = std::mem::take(&mut workspace.monomial_sorted_scratch);
    sorted.clear();
    sorted.reserve(all_monomials.len());
    sorted.extend(all_monomials.drain());
    sorted.sort_unstable_by(|a, b| b.cmp(a)); // descending
    workspace.all_monomials_scratch = all_monomials;

    let mut monomial_to_col = std::mem::take(&mut workspace.monomial_to_col_scratch);
    monomial_to_col.clear();
    monomial_to_col.reserve(sorted.len());
    let mut col_to_monomial = std::mem::take(&mut workspace.col_to_monomial_scratch);
    col_to_monomial.clear();
    col_to_monomial.reserve(sorted.len());
    for k in sorted.drain(..) {
        let col = col_to_monomial.len();
        col_to_monomial.push(k.mono().clone());
        monomial_to_col.insert(k, col);
    }
    workspace.monomial_sorted_scratch = sorted;

    // Mark which columns correspond to reducer LTs (i.e. monomials
    // divisible by some active basis LT). After row reduction, any
    // S-poly residue whose LT column is in this set is redundant
    // (its LT is divisible by an existing basis element).
    let mut reducer_cols = std::mem::take(&mut workspace.reducer_cols_scratch);
    reducer_cols.clear();
    reducer_cols.reserve(reducer_lts.len());
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
            // Correct echelon eliminates any row whose LT matches a
            // reducer pivot. This branch is unreachable from sound
            // input; skip rather than emit a redundant generator.
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
    // Return owned scratch buffers to the workspace so their
    // allocator capacity is reused on the next batch in this run.
    // `reducer_lts` / `reducer_basis_idx` were owned by the
    // workspace's `*_scratch` Vecs at function entry; put them back.
    workspace.monomial_to_col_scratch = monomial_to_col;
    workspace.col_to_monomial_scratch = col_to_monomial;
    workspace.reducer_cols_scratch = reducer_cols;
    workspace.reducer_lts_scratch = reducer_lts;
    workspace.reducer_basis_idx_scratch = reducer_basis_idx;
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
    spolys: Vec<DensePoly>,
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
    workspace: &mut F4Workspace,
) -> (Vec<DensePoly>, usize, Vec<Monomial>, Vec<usize>) {
    let n_spolys = spolys.len();
    // Destructure-borrow `workspace` so the reducer cache and the
    // per-batch scratch buffers are held as independent `&mut`
    // references. `reducer_lts_scratch` and `reducer_basis_idx_scratch`
    // are `mem::take`-d here and moved out via the return tuple;
    // `process_batch_with_workspace` assigns them back into the
    // workspace at end-of-call so allocator capacity persists.
    let F4Workspace {
        reducer_cache,
        stats,
        handled_scratch,
        worklist_scratch,
        reducer_lts_scratch,
        reducer_basis_idx_scratch,
        ..
    } = workspace;
    handled_scratch.clear();
    worklist_scratch.clear();
    let mut reducer_lts = std::mem::take(reducer_lts_scratch);
    let mut reducer_basis_idx = std::mem::take(reducer_basis_idx_scratch);
    reducer_lts.clear();
    reducer_basis_idx.clear();

    for poly in &spolys {
        for k in 0..poly.num_terms() {
            let mono = poly.term(k, ring).monomial();
            let key = MonoKey::new(mono.clone(), ring.order);
            if handled_scratch.insert(key) {
                worklist_scratch.push(mono);
            }
        }
    }
    let mut all_polys: Vec<DensePoly> = spolys;

    let mut idx = 0;
    while idx < worklist_scratch.len() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return (all_polys, n_spolys, reducer_lts, reducer_basis_idx);
        }
        let m = worklist_scratch[idx].clone();
        idx += 1;
        let m_key = MonoKey::new(m.clone(), ring.order);

        // Cache lookup. An entry maps `m` to `(bi, reducer_poly)`
        // where `bi` was the lowest-index active basis member whose
        // LT divided `m` at insertion time. Soundness invariant: the
        // basis is append-only and `m`'s divisor set is monotone
        // non-decreasing, so the chosen `bi` remains correct while
        // `basis[bi].active` holds. A deactivated `bi` falls through
        // to recomputation against the current active set.
        let cached = reducer_cache.get(&m_key).and_then(|(bi, poly)| {
            if basis.get(*bi).map(|b| b.active).unwrap_or(false) {
                Some((*bi, poly.clone()))
            } else {
                None
            }
        });
        if let Some((bi, reducer)) = cached {
            stats.reducer_hits += 1;
            reducer_lts.push(m.clone());
            reducer_basis_idx.push(bi);
            for k in 0..reducer.num_terms() {
                let mono = reducer.term(k, ring).monomial();
                let key = MonoKey::new(mono.clone(), ring.order);
                if handled_scratch.insert(key) {
                    worklist_scratch.push(mono);
                }
            }
            all_polys.push(reducer);
            continue;
        }
        // A cache entry whose `basis_idx` is no longer active
        // increments `stats.reducer_stale`. `stats.reducer_misses`
        // counts first-time lookups that produce a reducer.
        let was_stale = reducer_cache.contains_key(&m_key);
        if was_stale {
            stats.reducer_stale += 1;
            reducer_cache.remove(&m_key);
        }

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
        if !was_stale {
            stats.reducer_misses += 1;
        }
        reducer_cache.insert(m_key, (bi, reducer.clone()));
        reducer_lts.push(m.clone());
        reducer_basis_idx.push(bi);
        for k in 0..reducer.num_terms() {
            let mono = reducer.term(k, ring).monomial();
            let key = MonoKey::new(mono.clone(), ring.order);
            if handled_scratch.insert(key) {
                worklist_scratch.push(mono);
            }
        }
        all_polys.push(reducer);
    }
    (all_polys, n_spolys, reducer_lts, reducer_basis_idx)
}



#[cfg(test)]
mod tests;
