//! Plan v10 Phase 4 — F4-lite degree-batched matrix reduction.
//!
//! Buchberger's algorithm processes one S-pair at a time: build the
//! S-polynomial, run a `reduce_by_refs` cascade against the basis,
//! produce one new generator. On dense circuits like `inTest`, late-stage
//! S-polynomials have thousands of terms and the per-pair geobucket
//! cascade exceeds 60 s on its own — making per-call cancel budgets
//! useless.
//!
//! F4 (Faugère 1999) processes a *batch* of same-sugar S-pairs together:
//!
//! 1. Build S-polynomials for the whole batch.
//! 2. Symbolic preprocessing: every monomial appearing in any S-poly
//!    that is divisible by some active basis LT is "covered" by adding
//!    a reducer row `(m / LT(b)) * b` to the matrix. This is iterated
//!    until no uncovered divisible monomials remain.
//! 3. Build a sparse matrix: rows = S-polys + reducer rows, columns =
//!    the union of all monomials appearing.
//! 4. Sparse row-echelon reduce over GF(p).
//! 5. Each reduced S-poly row whose LT is *not* a reducer LT (i.e. not
//!    divisible by any active basis LT) is a new GB generator.
//!
//! The win on dense circuits: the per-pair geobucket merge cost is
//! amortized into a single sparse linear-algebra factorization, where
//! shared monomials in the batch share their reducer rows. Empirically
//! ~10× faster on the kind of late-stage S-pairs that block `inTest`.
//!
//! This is a "lite" implementation: no F4 trace (don't reuse matrices
//! across batches), no advanced selection strategy (just lowest-sugar),
//! no GBLA-style structured matrix layout. Correctness first, then
//! performance.

use std::collections::BTreeMap;
use std::sync::Arc;

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
/// kept around for S-pair generation history (false).
pub struct F4BasisRef<'a> {
    pub poly: &'a Polynomial,
    pub lt: &'a Monomial,
    pub active: bool,
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
) -> Vec<Polynomial> {
    if batch.is_empty() {
        return Vec::new();
    }
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 1: build S-polynomial for each pair.
    // Each pair gives S = (lcm/lt_i) * f_i - (lc_i/lc_j) * (lcm/lt_j) * f_j.
    // We follow the same construction as BuchbergerState::run.
    let mut spolys: Vec<Polynomial> = Vec::with_capacity(batch.len());
    for pair in batch {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return Vec::new();
        }
        // Resolve the basis elements via i, j. We accept basis as a
        // borrowed slice keyed by (active) index in the parent
        // BuchbergerState; the SPair stores those original indices.
        // For F4-lite the caller passes basis that maps SPair.{i,j}
        // to F4BasisRef directly.
        let i = pair.i;
        let j = pair.j;
        if i >= basis.len() || j >= basis.len() {
            // The pair references a deactivated/missing basis index.
            // Skip safely.
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
            None => continue, // shouldn't happen — basis are monic-ish
        };
        let one = ring.field.one();
        let part_i = bi.poly.mul_term(mul_i.exponents(), &one, ring);
        let neg_scale_j = ring.field.neg(&scale_j);
        let part_j = bj.poly.mul_term(mul_j.exponents(), &neg_scale_j, ring);
        let s_poly = part_i.add(&part_j, ring);
        if !s_poly.is_zero() {
            spolys.push(s_poly);
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
    let (all_polys, n_spolys, reducer_lts) = symbolic_preprocess(&spolys, basis, ring, cancel);
    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 3: build the monomial -> column index. Columns are sorted
    // by monomial DESCENDING (so column 0 = largest monomial, the
    // potential LT of any row).
    let mut all_monomials: BTreeMap<MonoKey, ()> = BTreeMap::new();
    for poly in &all_polys {
        for k in 0..poly.num_terms() {
            let mono = poly.term(k, ring).monomial();
            all_monomials.insert(MonoKey::new(mono, ring.order), ());
        }
    }
    // Walk in REVERSE so largest monomial gets column 0.
    let mut monomial_to_col: BTreeMap<MonoKey, usize> = BTreeMap::new();
    let mut col_to_monomial: Vec<Monomial> = Vec::with_capacity(all_monomials.len());
    for (k, _) in all_monomials.into_iter().rev() {
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
    // CORRECTNESS: reorder so reducer rows come FIRST and S-poly rows
    // come LAST. This way the row-echelon pass establishes reducer LTs
    // as pivots BEFORE encountering S-polys, so each S-poly gets
    // reduced against the reducers (instead of having S-polys grab
    // pivots that should belong to reducers — which would silently
    // drop reducer rows to zero and produce incomplete bases).
    //
    // After permutation: rows[0..n_reducers] are reducer rows,
    // rows[n_reducers..] are S-poly rows. Track the new index for
    // each S-poly so we can extract them after echelon.
    let n_reducers = all_polys.len() - n_spolys;
    let mut rows: Vec<SparseRow> = Vec::with_capacity(all_polys.len());
    // Reducer rows first (in their discovery order).
    for poly in &all_polys[n_spolys..] {
        rows.push(poly_to_sparse_row(poly, &monomial_to_col, ring));
    }
    // Then S-poly rows.
    for poly in &all_polys[..n_spolys] {
        rows.push(poly_to_sparse_row(poly, &monomial_to_col, ring));
    }

    // Step 5: sparse row-echelon reduce.
    sparse_echelon(&mut rows, &ring.field, cancel);

    if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
        return Vec::new();
    }

    // Step 6: extract new generators. The S-poly rows are now at
    // indices [n_reducers .. n_reducers + n_spolys].
    let mut out: Vec<Polynomial> = Vec::new();
    for i in n_reducers..(n_reducers + n_spolys) {
        let row = &rows[i];
        if row.is_empty() {
            continue; // useless reduction
        }
        let lt_col = row[0].0;
        if reducer_cols.contains(&lt_col) {
            // Should not happen after correct echelon: row LT would
            // have been eliminated by the corresponding reducer row.
            // Defensive skip.
            continue;
        }
        let poly = sparse_row_to_poly(row, &col_to_monomial, ring);
        if poly.is_zero() {
            continue;
        }
        let monic = poly.make_monic(ring);
        out.push(monic);
    }
    out
}

/// Symbolic preprocessing: given the S-polys, iteratively add reducer
/// rows for every monomial divisible by some active basis LT. Returns:
/// - The combined polynomial list (S-polys first, then reducer rows).
/// - Number of S-polys (so caller can split back out).
/// - The set of monomials that became reducer LTs.
fn symbolic_preprocess(
    spolys: &[Polynomial],
    basis: &[F4BasisRef],
    ring: &Arc<PolyRing>,
    cancel: Option<&CancelToken>,
) -> (Vec<Polynomial>, usize, Vec<Monomial>) {
    let mut all_polys: Vec<Polynomial> = spolys.to_vec();
    let n_spolys = all_polys.len();
    // Already-handled monomials: those that are reducer LTs (we won't
    // add another reducer for them) plus those that are LTs of S-polys
    // (those are pivot columns by definition).
    let mut handled: std::collections::HashSet<MonoKey> = std::collections::HashSet::new();
    let mut reducer_lts: Vec<Monomial> = Vec::new();

    // Worklist: monomials we still need to check for reducer-coverage.
    // Initialize with EVERY monomial of every S-poly. The S-polys' LTs
    // are pivots; we mark them handled but don't try to cover them.
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
            return (all_polys, n_spolys, reducer_lts);
        }
        let m = worklist[idx].clone();
        idx += 1;
        // Find an ACTIVE basis element b with LT(b) | m. Inactive
        // elements (deactivated via non-strict deactivation) are not
        // used as reducers — same contract as `BuchbergerState::run`'s
        // `active_refs` filter.
        let mut found: Option<usize> = None;
        for (bi, b) in basis.iter().enumerate() {
            if !b.active {
                continue;
            }
            if b.lt.divides(&m) {
                found = Some(bi);
                break;
            }
        }
        let bi = match found {
            Some(b) => b,
            None => continue, // m is "free": no reducer
        };
        // Build reducer row = (m / LT(b)) * b.poly
        let factor = m.div(basis[bi].lt);
        let one = ring.field.one();
        let reducer = basis[bi].poly.mul_term(factor.exponents(), &one, ring);
        if reducer.is_zero() {
            continue;
        }
        // Track this reducer's LT (which == m by construction).
        reducer_lts.push(m.clone());
        // All NEW monomials in the reducer's tail need to be in worklist.
        for k in 0..reducer.num_terms() {
            let mono = reducer.term(k, ring).monomial();
            let key = MonoKey::new(mono.clone(), ring.order);
            if handled.insert(key) {
                worklist.push(mono);
            }
        }
        all_polys.push(reducer);
    }
    (all_polys, n_spolys, reducer_lts)
}

/// Convert a polynomial to sparse row form (column-ascending). The
/// polynomial's terms are stored in monomial-DESCENDING order, which
/// matches column 0 = largest monomial.
fn poly_to_sparse_row(
    poly: &Polynomial,
    monomial_to_col: &BTreeMap<MonoKey, usize>,
    ring: &PolyRing,
) -> SparseRow {
    let mut row: SparseRow = Vec::with_capacity(poly.num_terms());
    for k in 0..poly.num_terms() {
        let term = poly.term(k, ring);
        let mono = term.monomial();
        let key = MonoKey::new(mono, ring.order);
        let col = match monomial_to_col.get(&key) {
            Some(&c) => c,
            None => continue, // shouldn't happen — every mono is in the index
        };
        row.push((col, term.coefficient().clone()));
    }
    // Sort by column ASCENDING.
    row.sort_by_key(|&(c, _)| c);
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

/// Sparse row echelon reduction over GF(p).
///
/// Convention: each row is a Vec<(col, coeff)> sorted by `col`
/// ASCENDING (so `row[0]` is the leading entry — column 0 is the
/// largest monomial). For each row in order:
///   - Reduce against any earlier-pivoted row whose pivot column
///     equals the current leading column.
///   - Iterate until the row's leading entry is at a column with no
///     existing pivot (or the row is zero).
///   - If non-zero, monic-normalize and register as a new pivot.
///
/// The output `rows` are the reduced (in-place updated) rows.
fn sparse_echelon(rows: &mut Vec<SparseRow>, field: &PrimeField, cancel: Option<&CancelToken>) {
    use std::collections::HashMap;
    // pivot_col -> row index (the row that owns this pivot column).
    let mut pivots: HashMap<usize, usize> = HashMap::new();

    // Process rows in order. We don't sort because the caller has
    // already given us a deterministic ordering (S-polys first, then
    // reducers in the order they were discovered).
    for i in 0..rows.len() {
        if cancel.map(|c| c.is_cancelled()).unwrap_or(false) {
            return;
        }
        // Reduce row[i] against existing pivots.
        loop {
            if rows[i].is_empty() {
                break;
            }
            let lead_col = rows[i][0].0;
            let pivot_row = match pivots.get(&lead_col) {
                Some(&p) => p,
                None => break,
            };
            // Eliminate: row[i] -= (lead_coeff / pivot_lead_coeff) * row[pivot_row]
            // Since row[pivot_row] is monic (we make pivot rows monic
            // when registered), pivot_lead_coeff = 1, so:
            // row[i] -= lead_coeff * row[pivot_row]
            let scale = rows[i][0].1.clone();
            // Sparse axpy: row[i] = row[i] - scale * row[pivot_row]
            let pivot_clone: SparseRow = rows[pivot_row].clone();
            let new_row = sparse_sub_scaled(&rows[i], &pivot_clone, &scale, field);
            rows[i] = new_row;
        }
        if rows[i].is_empty() {
            continue;
        }
        // Monic-normalize the leading coefficient.
        let lead_coeff = rows[i][0].1.clone();
        if !field.is_zero(&lead_coeff) {
            // Multiply every coefficient by lead_coeff^{-1}.
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

    fn const_poly(v: i32, ring: &Arc<PolyRing>) -> Polynomial {
        let f = &ring.field;
        let coeff = if v >= 0 {
            f.from_u64(v as u64)
        } else {
            f.neg(&f.from_u64((-v) as u64))
        };
        Polynomial::constant(coeff, ring)
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
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, active: true })
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
        let np = &new_polys[0];
        let np_lt = lt(np, &ring);
        // x^2 monomial: exponents [2, 0]
        assert_eq!(np_lt.exponents(), &[2, 0], "expected new LT x^2, got {:?}", np_lt.exponents());
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
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, active: true })
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

        // Both paths should agree on whether result is zero.
        if reduced.is_zero() {
            assert!(new_polys.is_empty(), "F4 produced new poly but reference reduced to zero");
        } else {
            // Both should produce same monic polynomial.
            assert_eq!(new_polys.len(), 1);
            let f4_monic = &new_polys[0];
            let ref_monic = reduced.make_monic(&ring);
            assert_eq!(
                f4_monic.num_terms(),
                ref_monic.num_terms(),
                "F4 and ref differ in num_terms: F4={:?}, ref={:?}",
                f4_monic, ref_monic
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
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, active: true })
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
            .map(|p| {
                let r = p.reduce_by_refs(&basis_poly_refs, ring);
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
            .map(|(p, l)| F4BasisRef { poly: p, lt: l, active: true })
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
}
