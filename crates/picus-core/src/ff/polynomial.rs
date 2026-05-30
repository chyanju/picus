//! Multivariate polynomials over GF(p) with explicit exponent vectors.
//!
//! Memory layout: `exponents` is a flat `Vec<u16>` of length `num_terms * n_vars`,
//! and `coeffs` is a `Vec<FieldElem>` of length `num_terms`. Term `i` has
//! exponents `exponents[i * n_vars .. (i+1) * n_vars]` and coefficient `coeffs[i]`.
//!
//! Terms are kept sorted in **descending** order under the ring's monomial order
//! (leading term at index 0). This is the opposite of feanor-math's storage but
//! is more cache-friendly for Buchberger reduction, where the leading term is
//! accessed on every iteration.
//!
//! Coefficients are always nonzero (zero terms eliminated during arithmetic).

use std::cmp::Ordering;
use std::sync::Arc;

use super::field::{FieldElem, PrimeField};
use super::monomial::{Monomial, MonomialOrder};
use super::divmask::DivMaskScheme;
use super::repr::MonomialRepr;
use super::sparse_monomial::SparseMonomial;
use super::sparse_polynomial::SparsePolynomial;
use crate::config::ReprKind;
use crate::metric;

/// Shared context describing the polynomial ring `GF(p)[x_0, ..., x_{n-1}]`.
///
/// All polynomials over the same ring share an `Arc<PolyRing>`. The ring carries
/// the field, the variable count, the term order, and the DivMask scheme.
#[derive(Debug)]
pub struct PolyRing {
    pub field: PrimeField,
    pub n_vars: usize,
    pub order: MonomialOrder,
    pub var_names: Vec<String>,
    pub divmask: DivMaskScheme,
    /// Storage representation for polynomials built over this ring,
    /// seeded from [`crate::config::RuntimeConfig::poly_repr`] at
    /// construction. `DensePoly` constructors consult it to build the
    /// dense flat or the sparse arm; the dense Gröbner engine only ever
    /// sees `Dense`-storage polynomials (the sparse path routes GB
    /// through `ff::sparse_gb`).
    pub repr: ReprKind,
}

impl PolyRing {
    pub fn new(field: PrimeField, var_names: Vec<String>, order: MonomialOrder) -> Arc<Self> {
        let repr = crate::config::with(|c| c.poly_repr);
        Self::new_with_repr(field, var_names, order, repr)
    }

    /// Like [`Self::new`] but with an explicit storage representation,
    /// bypassing the thread-local `config::poly_repr`. Lets callers (tests,
    /// the differential oracle) pin a representation without mutating global
    /// config.
    pub fn new_with_repr(
        field: PrimeField,
        var_names: Vec<String>,
        order: MonomialOrder,
        repr: ReprKind,
    ) -> Arc<Self> {
        let n_vars = var_names.len();
        // Heuristic exponent cap: monomials beyond degree 16 in any
        // single variable are rare for the inputs the solver sees.
        let divmask = DivMaskScheme::build(n_vars, 16);
        Arc::new(PolyRing { field, n_vars, order, var_names, divmask, repr })
    }

    pub fn with_divmask(
        field: PrimeField,
        var_names: Vec<String>,
        order: MonomialOrder,
        max_deg_hint: u16,
    ) -> Arc<Self> {
        let n_vars = var_names.len();
        let divmask = DivMaskScheme::build(n_vars, max_deg_hint);
        let repr = crate::config::with(|c| c.poly_repr);
        Arc::new(PolyRing { field, n_vars, order, var_names, divmask, repr })
    }
}

/// A multivariate polynomial in flat storage.
#[derive(Clone, Debug)]
pub struct DensePoly {
    /// Flat exponent storage, length `num_terms * ring.n_vars`.
    exponents: Vec<u16>,
    /// Coefficients, length `num_terms`. All nonzero.
    coeffs: Vec<FieldElem>,
    /// Cached total degree per term (length `num_terms`).
    total_degs: Vec<u32>,
}

/// The solve core's polynomial: a runtime dense/sparse union so a ring
/// built under `ReprKind::Sparse` keeps its polynomials resident-sparse
/// on wide rings (no O(n_vars)-per-term dense exponent vectors), while a
/// `Dense` ring keeps the cache-friendly flat layout the Gröbner engine
/// is tuned for. The arm is fixed per ring (constructors consult
/// `ring.repr`), so values built over one ring share one arm.
///
/// Common ops (arithmetic, leading term, reduction, monic) dispatch to a
/// representation-native implementation. The few dense-flavoured readers
/// (`TermRef` iteration, raw exponent access, `substitute_var`, …) fall
/// back to a one-shot dense materialisation on the sparse arm — correct,
/// and off the resident-memory path. The dense Gröbner engine
/// (`buchberger`, `geobucket`) works on `DensePoly` directly and never
/// sees the sparse arm (the sparse path routes GB through `ff::sparse_gb`).
#[derive(Clone, Debug)]
pub enum Polynomial {
    Dense(DensePoly),
    Sparse(SparsePolynomial),
}

impl Polynomial {
    /// Coerce to the ring's configured arm (no-op when already correct).
    /// Used to reconcile a representation-neutral `zero()` with operands
    /// built over the ring.
    fn into_arm(self, ring: &PolyRing) -> Polynomial {
        match (self, ring.repr) {
            (Polynomial::Dense(d), ReprKind::Sparse) => {
                Polynomial::Sparse(SparsePolynomial::from_dense(&d, ring))
            }
            (Polynomial::Sparse(s), ReprKind::Dense) => Polynomial::Dense(s.to_dense(ring)),
            (p, _) => p,
        }
    }

    /// View as the dense arm, materialising the sparse arm if needed.
    /// For the rare dense-flavoured readers.
    pub fn as_dense(&self, ring: &PolyRing) -> std::borrow::Cow<'_, DensePoly> {
        match self {
            Polynomial::Dense(d) => std::borrow::Cow::Borrowed(d),
            Polynomial::Sparse(s) => std::borrow::Cow::Owned(s.to_dense(ring)),
        }
    }

    // ── constructors (arm chosen by ring.repr) ──────────────────────
    pub fn zero() -> Self {
        // Representation-neutral empty; binary ops coerce it to the
        // ring's arm via `into_arm`.
        Polynomial::Dense(DensePoly::zero())
    }
    pub fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        match ring.repr {
            ReprKind::Dense => Polynomial::Dense(DensePoly::constant(c, ring)),
            ReprKind::Sparse => Polynomial::Sparse(SparsePolynomial::constant(c, ring)),
        }
    }
    pub fn variable(var: usize, ring: &PolyRing) -> Self {
        match ring.repr {
            ReprKind::Dense => Polynomial::Dense(DensePoly::variable(var, ring)),
            ReprKind::Sparse => Polynomial::Sparse(SparsePolynomial::variable(var, ring)),
        }
    }
    pub fn from_terms(terms: Vec<(Monomial, FieldElem)>, ring: &PolyRing) -> Self {
        match ring.repr {
            ReprKind::Dense => Polynomial::Dense(DensePoly::from_terms(terms, ring)),
            ReprKind::Sparse => {
                let sterms: Vec<(SparseMonomial, FieldElem)> = terms
                    .into_iter()
                    .map(|(m, c)| (SparseMonomial::from_exponents(m.exponents().to_vec()), c))
                    .collect();
                Polynomial::Sparse(SparsePolynomial::from_terms(sterms, ring))
            }
        }
    }

    // ── queries ─────────────────────────────────────────────────────
    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            Polynomial::Dense(d) => d.is_zero(),
            Polynomial::Sparse(s) => s.is_zero(),
        }
    }
    pub fn num_terms(&self) -> usize {
        match self {
            Polynomial::Dense(d) => d.num_terms(),
            Polynomial::Sparse(s) => s.num_terms(),
        }
    }
    pub fn is_constant(&self) -> bool {
        match self {
            Polynomial::Dense(d) => d.is_constant(),
            Polynomial::Sparse(s) => s.is_constant(),
        }
    }
    #[inline]
    pub fn total_degree(&self) -> u32 {
        match self {
            Polynomial::Dense(d) => d.total_degree(),
            Polynomial::Sparse(s) => s.total_degree(),
        }
    }
    #[inline]
    pub fn leading_coefficient(&self) -> Option<&FieldElem> {
        match self {
            Polynomial::Dense(d) => d.leading_coefficient(),
            Polynomial::Sparse(s) => s.leading_coefficient(),
        }
    }
    #[inline]
    pub fn leading_monomial(&self, ring: &PolyRing) -> Option<Monomial> {
        match self {
            Polynomial::Dense(d) => d.leading_monomial(ring),
            Polynomial::Sparse(s) => {
                s.leading_monomial().map(|m| Monomial::from_exponents(MonomialRepr::to_dense(m)))
            }
        }
    }

    // ── arithmetic (operands coerced to a common arm) ───────────────
    pub fn add(&self, other: &Self, ring: &PolyRing) -> Self {
        match (self, other) {
            (Polynomial::Dense(a), Polynomial::Dense(b)) => Polynomial::Dense(a.add(b, ring)),
            (Polynomial::Sparse(a), Polynomial::Sparse(b)) => Polynomial::Sparse(a.add(b, ring)),
            _ => self.clone().into_arm(ring).add(&other.clone().into_arm(ring), ring),
        }
    }
    pub fn sub(&self, other: &Self, ring: &PolyRing) -> Self {
        match (self, other) {
            (Polynomial::Dense(a), Polynomial::Dense(b)) => Polynomial::Dense(a.sub(b, ring)),
            (Polynomial::Sparse(a), Polynomial::Sparse(b)) => Polynomial::Sparse(a.sub(b, ring)),
            _ => self.clone().into_arm(ring).sub(&other.clone().into_arm(ring), ring),
        }
    }
    pub fn mul(&self, other: &Self, ring: &PolyRing) -> Self {
        match (self, other) {
            (Polynomial::Dense(a), Polynomial::Dense(b)) => Polynomial::Dense(a.mul(b, ring)),
            (Polynomial::Sparse(a), Polynomial::Sparse(b)) => Polynomial::Sparse(a.mul(b, ring)),
            _ => self.clone().into_arm(ring).mul(&other.clone().into_arm(ring), ring),
        }
    }
    pub fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Self {
        match self {
            Polynomial::Dense(d) => Polynomial::Dense(d.scale(c, ring)),
            Polynomial::Sparse(s) => Polynomial::Sparse(s.scale(c, ring)),
        }
    }
    pub fn negate(&self, ring: &PolyRing) -> Self {
        match self {
            Polynomial::Dense(d) => Polynomial::Dense(d.negate(ring)),
            Polynomial::Sparse(s) => Polynomial::Sparse(s.negate(ring)),
        }
    }
    pub fn make_monic(&self, ring: &PolyRing) -> Self {
        match self {
            Polynomial::Dense(d) => Polynomial::Dense(d.make_monic(ring)),
            Polynomial::Sparse(s) => Polynomial::Sparse(s.make_monic(ring)),
        }
    }
    pub fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem {
        match self {
            Polynomial::Dense(d) => d.evaluate(values, ring),
            Polynomial::Sparse(s) => s.evaluate(values, ring),
        }
    }

    // ── reduction (normal form modulo divisors) ─────────────────────
    pub fn reduce_by(&self, divisors: &[Polynomial], ring: &PolyRing) -> Self {
        let refs: Vec<&Polynomial> = divisors.iter().collect();
        self.reduce_by_refs(&refs, ring)
    }
    pub fn reduce_by_refs(&self, divisors: &[&Polynomial], ring: &PolyRing) -> Self {
        match self {
            Polynomial::Sparse(s) => {
                let ds: Vec<SparsePolynomial> =
                    divisors.iter().map(|p| p.to_sparse(ring)).collect();
                let dr: Vec<&SparsePolynomial> = ds.iter().collect();
                Polynomial::Sparse(s.reduce_by_refs(&dr, ring))
            }
            Polynomial::Dense(d) => {
                let ds: Vec<std::borrow::Cow<DensePoly>> =
                    divisors.iter().map(|p| p.as_dense(ring)).collect();
                let dr: Vec<&DensePoly> = ds.iter().map(|c| c.as_ref()).collect();
                Polynomial::Dense(d.reduce_by_refs(&dr, ring))
            }
        }
    }
    pub fn reduce_by_refs_cancel(
        &self,
        divisors: &[&Polynomial],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
    ) -> Self {
        match self {
            Polynomial::Sparse(s) => {
                let ds: Vec<SparsePolynomial> =
                    divisors.iter().map(|p| p.to_sparse(ring)).collect();
                let dr: Vec<&SparsePolynomial> = ds.iter().collect();
                Polynomial::Sparse(s.reduce_by_refs_cancel(&dr, ring, Some(cancel)))
            }
            Polynomial::Dense(d) => {
                let ds: Vec<std::borrow::Cow<DensePoly>> =
                    divisors.iter().map(|p| p.as_dense(ring)).collect();
                let dr: Vec<&DensePoly> = ds.iter().map(|c| c.as_ref()).collect();
                Polynomial::Dense(d.reduce_by_refs_cancel(&dr, ring, cancel))
            }
        }
    }

    /// Convert to the sparse representation (boundary helper).
    pub fn to_sparse(&self, ring: &PolyRing) -> SparsePolynomial {
        match self {
            Polynomial::Sparse(s) => s.clone(),
            Polynomial::Dense(d) => SparsePolynomial::from_dense(d, ring),
        }
    }

    // ── dense-flavoured readers (sparse arm materialises) ───────────
    pub fn appearing_variables(&self, ring: &PolyRing) -> Vec<(usize, u16)> {
        match self {
            Polynomial::Dense(d) => d.appearing_variables(ring),
            Polynomial::Sparse(s) => s.appearing_variables(),
        }
    }
    pub fn substitute_var(&self, var: usize, value: &FieldElem, ring: &PolyRing) -> Self {
        match self {
            Polynomial::Dense(d) => Polynomial::Dense(d.substitute_var(var, value, ring)),
            Polynomial::Sparse(s) => {
                Polynomial::Sparse(SparsePolynomial::from_dense(
                    &s.to_dense(ring).substitute_var(var, value, ring),
                    ring,
                ))
            }
        }
    }
    pub fn is_univariate(&self, ring: &PolyRing) -> Option<usize> {
        self.as_dense(ring).is_univariate(ring)
    }
    pub fn content_hash(&self) -> u64 {
        match self {
            Polynomial::Dense(d) => d.content_hash(),
            Polynomial::Sparse(s) => s.content_hash(),
        }
    }
    /// Each term as `(coeff, sorted nonzero (var, exp) pairs)` — the
    /// representation-native read the IR lowering / SMT backends use.
    pub fn collect_terms_idx(
        &self,
        ctx: &PolyRing,
    ) -> Vec<(num_bigint::BigUint, Vec<(usize, u16)>)> {
        match self {
            Polynomial::Dense(d) => <DensePoly as super::repr::PolyRepr>::collect_terms_idx(d, ctx),
            Polynomial::Sparse(s) => {
                <SparsePolynomial as super::repr::PolyRepr>::collect_terms_idx(s, ctx)
            }
        }
    }
}

/// A lightweight reference to a single term within a polynomial.
#[derive(Copy, Clone, Debug)]
pub struct TermRef<'a> {
    poly: &'a DensePoly,
    n_vars: usize,
    idx: usize,
}

impl<'a> TermRef<'a> {
    #[inline]
    pub fn coefficient(&self) -> &'a FieldElem {
        &self.poly.coeffs[self.idx]
    }

    #[inline]
    pub fn total_degree(&self) -> u32 {
        self.poly.total_degs[self.idx]
    }

    #[inline]
    pub fn exponents(&self) -> &'a [u16] {
        let start = self.idx * self.n_vars;
        &self.poly.exponents[start..start + self.n_vars]
    }

    #[inline]
    pub fn exponent(&self, var: usize) -> u16 {
        self.poly.exponents[self.idx * self.n_vars + var]
    }

    pub fn monomial(&self) -> Monomial {
        Monomial::from_exponents(self.exponents().to_vec())
    }
}

/// Prebuilt divisor-lookup structure for the geobucket reducer, owning its
/// data so it can be **cached across reduce calls** whose divisor set is
/// unchanged (the Buchberger active basis between basis mutations). Mirrors
/// the per-call structure that `reduce_by_refs_geobucket` builds: a degree-
/// sorted `order` (from `SORT_THRESHOLD` divisors) and DivMask `buckets`
/// (from `BUCKET_THRESHOLD`). The leading *coefficient* is NOT stored — it is
/// read lazily from the live divisor at reduce time, matching the per-call
/// reducer. Built by [`ReducerIndex::build`], consumed by
/// [`DensePoly::reduce_by_refs_geobucket_indexed`].
pub struct ReducerIndex {
    /// Per divisor `i`: `(owned LT exponents, LT total degree, LT DivMask)`,
    /// or `None` if the divisor was zero.
    div_lt: Vec<Option<(Vec<u16>, u32, super::divmask::DivMask)>>,
    /// Degree-ascending order of divisor indices (early-break scan), present
    /// at `>= SORT_THRESHOLD` divisors.
    order: Option<Vec<usize>>,
    /// DivMask-keyed buckets (each sorted by LT degree), present at
    /// `>= BUCKET_THRESHOLD` divisors.
    buckets: Option<std::collections::HashMap<u128, Vec<usize>>>,
}

impl ReducerIndex {
    /// Divisor count from which the degree-`order` index is built. Single
    /// source for this threshold, shared with the inline index built in
    /// `reduce_by_refs_geobucket`.
    pub const SORT_THRESHOLD: usize = 64;
    /// Divisor count from which the DivMask bucket index is built. Single
    /// source for this threshold, shared with the inline index built in
    /// `reduce_by_refs_geobucket`.
    pub const BUCKET_THRESHOLD: usize = 256;

    /// Build the index over `divisors` (in caller order). `div_dms[i]`, when
    /// supplied, is divisor `i`'s precomputed leading-term DivMask. Exponent
    /// vectors are cloned (owned) so the index outlives the `divisors` borrow.
    pub fn build(
        divisors: &[&DensePoly],
        ring: &PolyRing,
        div_dms: Option<&[super::divmask::DivMask]>,
    ) -> Self {
        use super::divmask::DivMask;
        let div_lt: Vec<Option<(Vec<u16>, u32, DivMask)>> = divisors
            .iter()
            .enumerate()
            .map(|(i, d)| {
                d.leading_term(ring).map(|lt| {
                    let exps = lt.exponents();
                    let dm = match div_dms {
                        Some(dms) => dms[i],
                        None => ring.divmask.compute_from_slice(exps),
                    };
                    (exps.to_vec(), lt.total_degree(), dm)
                })
            })
            .collect();
        let order = if div_lt.len() >= Self::SORT_THRESHOLD {
            let mut o: Vec<usize> = (0..div_lt.len()).collect();
            o.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
            Some(o)
        } else {
            None
        };
        let buckets = if div_lt.len() >= Self::BUCKET_THRESHOLD {
            let mut b: std::collections::HashMap<u128, Vec<usize>> =
                std::collections::HashMap::new();
            for (i, lt_opt) in div_lt.iter().enumerate() {
                if let Some((_, _, dm)) = lt_opt {
                    b.entry(dm.0).or_default().push(i);
                }
            }
            for indices in b.values_mut() {
                indices.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
            }
            Some(b)
        } else {
            None
        };
        ReducerIndex { div_lt, order, buckets }
    }

    /// Number of divisors the index was built over.
    pub fn len(&self) -> usize {
        self.div_lt.len()
    }

    /// `true` when the index is empty.
    pub fn is_empty(&self) -> bool {
        self.div_lt.is_empty()
    }

    /// Whether the cached leading-term data still matches `divisors`'
    /// current leading terms (exponents + degree). A debug-only staleness
    /// guard for the Buchberger cache: an unchanged active-index set must
    /// imply unchanged leading terms (tail reduction preserves them).
    pub fn matches_active(&self, divisors: &[&DensePoly], ring: &PolyRing) -> bool {
        if self.div_lt.len() != divisors.len() {
            return false;
        }
        for (entry, d) in self.div_lt.iter().zip(divisors.iter()) {
            match (entry, d.leading_term(ring)) {
                (Some((exps, deg, _)), Some(lt)) => {
                    if exps.as_slice() != lt.exponents() || *deg != lt.total_degree() {
                        return false;
                    }
                }
                (None, None) => {}
                _ => return false,
            }
        }
        true
    }
}

impl DensePoly {
    /// The zero polynomial.
    pub fn zero() -> Self {
        DensePoly { exponents: Vec::new(), coeffs: Vec::new(), total_degs: Vec::new() }
    }

    /// Construct a constant polynomial. Returns the zero polynomial if `c` is zero.
    pub fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        if ring.field.is_zero(&c) {
            return DensePoly::zero();
        }
        DensePoly {
            exponents: vec![0u16; ring.n_vars],
            coeffs: vec![c],
            total_degs: vec![0],
        }
    }

    /// Construct from a list of `(monomial, coefficient)` pairs. Zero coefficients
    /// are discarded; like-monomials are summed; result is sorted descending.
    pub fn from_terms(terms: Vec<(Monomial, FieldElem)>, ring: &PolyRing) -> Self {
        let mut filtered: Vec<(Monomial, FieldElem)> = terms
            .into_iter()
            .filter(|(_, c)| !ring.field.is_zero(c))
            .collect();
        // Sort descending by ring order. Stable sort to be predictable.
        filtered.sort_by(|a, b| b.0.cmp_with_order(&a.0, ring.order));
        // Combine consecutive equal monomials.
        let mut out_exps: Vec<u16> = Vec::with_capacity(filtered.len() * ring.n_vars);
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(filtered.len());
        let mut out_degs: Vec<u32> = Vec::with_capacity(filtered.len());
        for (mon, coeff) in filtered.into_iter() {
            if let Some(last_deg) = out_degs.last().copied() {
                let last_start = (out_coeffs.len() - 1) * ring.n_vars;
                let last_exps = &out_exps[last_start..last_start + ring.n_vars];
                if last_deg == mon.total_degree() && last_exps == mon.exponents() {
                    let combined = ring.field.add(out_coeffs.last().unwrap(), &coeff);
                    if ring.field.is_zero(&combined) {
                        // Cancellation — drop the term entirely.
                        out_coeffs.pop();
                        out_degs.pop();
                        out_exps.truncate(last_start);
                    } else {
                        *out_coeffs.last_mut().unwrap() = combined;
                    }
                    continue;
                }
            }
            out_exps.extend_from_slice(mon.exponents());
            out_coeffs.push(coeff);
            out_degs.push(mon.total_degree());
        }
        DensePoly { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Construct from already-sorted (descending) parallel arrays. UB if violated.
    pub fn from_raw_sorted(
        exponents: Vec<u16>,
        coeffs: Vec<FieldElem>,
        total_degs: Vec<u32>,
    ) -> Self {
        debug_assert_eq!(coeffs.len(), total_degs.len());
        if !coeffs.is_empty() {
            debug_assert_eq!(exponents.len() / coeffs.len() * coeffs.len(), exponents.len());
        }
        // No total-degree monotonicity check: "descending" is by the ring's
        // monomial order, which implies non-increasing total degree under
        // DegRevLex but not under Lex (e.g. `x0` > `x1^5` in Lex, yet has lower
        // degree). This function holds no ring and so cannot validate the
        // order-relative descent; callers build these arrays by popping the
        // geobucket in `ring.order` and own that contract.
        DensePoly { exponents, coeffs, total_degs }
    }

    /// `x_var` as a monomial polynomial with coefficient 1.
    pub fn variable(var: usize, ring: &PolyRing) -> Self {
        let mut exps = vec![0u16; ring.n_vars];
        exps[var] = 1;
        DensePoly {
            exponents: exps,
            coeffs: vec![ring.field.one()],
            total_degs: vec![1],
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    #[inline]
    pub fn num_terms(&self) -> usize {
        self.coeffs.len()
    }

    pub fn is_constant(&self) -> bool {
        match self.coeffs.len() {
            0 => true,
            1 => self.total_degs[0] == 0,
            _ => false,
        }
    }

    pub fn term(&self, idx: usize, ring: &PolyRing) -> TermRef<'_> {
        TermRef { poly: self, n_vars: ring.n_vars, idx }
    }

    pub fn leading_term(&self, ring: &PolyRing) -> Option<TermRef<'_>> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.term(0, ring))
        }
    }

    #[inline]
    pub fn leading_coefficient(&self) -> Option<&FieldElem> {
        self.coeffs.first()
    }

    #[inline]
    pub fn leading_monomial(&self, ring: &PolyRing) -> Option<Monomial> {
        self.leading_term(ring).map(|t| t.monomial())
    }

    /// Maximum total degree across all terms.
    #[inline]
    pub fn total_degree(&self) -> u32 {
        self.total_degs.first().copied().unwrap_or(0)
    }

    /// Cheap structural fingerprint suitable as a memoisation key.
    ///
    /// Hashes the exponent layout + per-term degrees + leading
    /// coefficient.
    /// Two distinct polynomials having the same `content_hash` is
    /// possible (it's a u64 hash, not a content-equality check) but
    /// astronomically unlikely within a single GB call. Used by
    /// `split_gb_extend_cancel` / `split_gb_cancel` to skip redundant
    /// `contains` checks across fixpoint iterations.
    ///
    /// **Soundness note**: a collision-induced false positive in the
    /// caller's memo causes a missed propagation step, which is sound
    /// (picus's UNSAT proofs require exhausting the DFS, and SAT
    /// verdicts are model-verified). Never flips a verdict.
    pub fn content_hash(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.exponents.hash(&mut h);
        self.total_degs.hash(&mut h);
        self.coeffs.len().hash(&mut h);
        // Mix in the leading coefficient for sensitivity to
        // coefficient changes between same-monomial polynomials.
        if let Some(lc) = self.coeffs.first() {
            lc.hash(&mut h);
        }
        h.finish()
    }

    /// Iterate terms in descending order.
    pub fn terms<'a>(&'a self, ring: &PolyRing) -> impl Iterator<Item = TermRef<'a>> + 'a {
        let n = ring.n_vars;
        (0..self.coeffs.len()).map(move |i| TermRef { poly: self, n_vars: n, idx: i })
    }

    #[inline]
    pub fn raw_exponents(&self) -> &[u16] { &self.exponents }
    #[inline]
    pub fn raw_coeffs(&self) -> &[FieldElem] { &self.coeffs }
    #[inline]
    pub fn raw_total_degs(&self) -> &[u32] { &self.total_degs }

    /// Negate every coefficient in place.
    pub fn negate_in_place(&mut self, ring: &PolyRing) {
        for c in self.coeffs.iter_mut() {
            *c = ring.field.neg(c);
        }
    }

    pub fn negate(&self, ring: &PolyRing) -> DensePoly {
        let mut out = self.clone();
        out.negate_in_place(ring);
        out
    }

    /// Multiply every coefficient by `c`. Returns zero if `c == 0`.
    pub fn scale(&self, c: &FieldElem, ring: &PolyRing) -> DensePoly {
        if ring.field.is_zero(c) {
            return DensePoly::zero();
        }
        if ring.field.is_one(c) {
            return self.clone();
        }
        let coeffs: Vec<FieldElem> = self.coeffs.iter().map(|x| ring.field.mul(x, c)).collect();
        DensePoly {
            exponents: self.exponents.clone(),
            coeffs,
            total_degs: self.total_degs.clone(),
        }
    }

    /// Make polynomial monic (divide by leading coefficient). No-op for zero.
    pub fn make_monic(&self, ring: &PolyRing) -> DensePoly {
        if self.is_zero() {
            return DensePoly::zero();
        }
        let lc = self.coeffs[0].clone();
        if ring.field.is_one(&lc) {
            return self.clone();
        }
        let lc_inv = ring.field.inv(&lc).expect("nonzero lc");
        self.scale(&lc_inv, ring)
    }

    /// Comparison helper between term `i` of `self` and term `j` of `other` under the ring order.
    #[inline]
    pub fn cmp_term_at(
        a_exps: &[u16],
        a_deg: u32,
        b_exps: &[u16],
        b_deg: u32,
        order: MonomialOrder,
    ) -> Ordering {
        match order {
            MonomialOrder::Lex => {
                for (x, y) in a_exps.iter().zip(b_exps.iter()) {
                    match x.cmp(y) {
                        Ordering::Equal => continue,
                        o => return o,
                    }
                }
                Ordering::Equal
            }
            MonomialOrder::DegRevLex => match a_deg.cmp(&b_deg) {
                Ordering::Equal => {
                    for (x, y) in a_exps.iter().rev().zip(b_exps.iter().rev()) {
                        match x.cmp(y) {
                            Ordering::Equal => continue,
                            Ordering::Less => return Ordering::Greater,
                            Ordering::Greater => return Ordering::Less,
                        }
                    }
                    Ordering::Equal
                }
                o => o,
            },
            MonomialOrder::Matrix(idx) => {
                super::matrix_order::resolve(idx).cmp_dense(a_exps, b_exps)
            }
        }
    }

    fn merge_sorted(&self, other: &DensePoly, ring: &PolyRing, negate_other: bool) -> DensePoly {
        let n = ring.n_vars;
        let mut out_exps: Vec<u16> = Vec::with_capacity(self.exponents.len() + other.exponents.len());
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(self.coeffs.len() + other.coeffs.len());
        let mut out_degs: Vec<u32> = Vec::with_capacity(self.coeffs.len() + other.coeffs.len());
        let (mut i, mut j) = (0usize, 0usize);
        let (la, lb) = (self.coeffs.len(), other.coeffs.len());
        while i < la && j < lb {
            let ae = &self.exponents[i * n..(i + 1) * n];
            let be = &other.exponents[j * n..(j + 1) * n];
            let ad = self.total_degs[i];
            let bd = other.total_degs[j];
            match Self::cmp_term_at(ae, ad, be, bd, ring.order) {
                Ordering::Greater => {
                    out_exps.extend_from_slice(ae);
                    out_coeffs.push(self.coeffs[i].clone());
                    out_degs.push(ad);
                    i += 1;
                }
                Ordering::Less => {
                    out_exps.extend_from_slice(be);
                    let c = if negate_other { ring.field.neg(&other.coeffs[j]) } else { other.coeffs[j].clone() };
                    out_coeffs.push(c);
                    out_degs.push(bd);
                    j += 1;
                }
                Ordering::Equal => {
                    let s = if negate_other {
                        ring.field.sub(&self.coeffs[i], &other.coeffs[j])
                    } else {
                        ring.field.add(&self.coeffs[i], &other.coeffs[j])
                    };
                    if !ring.field.is_zero(&s) {
                        out_exps.extend_from_slice(ae);
                        out_coeffs.push(s);
                        out_degs.push(ad);
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < la {
            let ae = &self.exponents[i * n..(i + 1) * n];
            out_exps.extend_from_slice(ae);
            out_coeffs.push(self.coeffs[i].clone());
            out_degs.push(self.total_degs[i]);
            i += 1;
        }
        while j < lb {
            let be = &other.exponents[j * n..(j + 1) * n];
            out_exps.extend_from_slice(be);
            let c = if negate_other { ring.field.neg(&other.coeffs[j]) } else { other.coeffs[j].clone() };
            out_coeffs.push(c);
            out_degs.push(other.total_degs[j]);
            j += 1;
        }
        DensePoly { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Merge-based addition. Both inputs are descending-sorted.
    pub fn add(&self, other: &DensePoly, ring: &PolyRing) -> DensePoly {
        self.merge_sorted(other, ring, false)
    }

    /// Move-based merge for cases where both inputs are owned. Recycles
    /// each input's `FieldElem` allocations into the output rather than
    /// cloning them, eliminating O(M + N) GMP `Integer` allocations
    /// per merge.
    pub fn merge_owned(self, other: DensePoly, ring: &PolyRing, negate_other: bool) -> DensePoly {
        if self.is_zero() {
            return if negate_other { other.negate(ring) } else { other };
        }
        if other.is_zero() {
            return self;
        }
        // Two counters under one gb-stats read (this is a hot cascade-merge
        // path); same single-read batching as the reducer drain.
        metric::scope! {
            let g = &crate::profile::SPLIT_GB;
            metric::add!(g.merge_owned_calls, 1);
            metric::add!(g.merge_owned_terms_total,
                (self.coeffs.len() + other.coeffs.len()) as u64);
        }
        let n = ring.n_vars;
        let la = self.coeffs.len();
        let lb = other.coeffs.len();
        let cap = la + lb;
        let mut out_exps: Vec<u16> = Vec::with_capacity(cap * n);
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(cap);
        let mut out_degs: Vec<u32> = Vec::with_capacity(cap);
        let a_exps = self.exponents;
        let a_degs = self.total_degs;
        let mut a_coeffs = self.coeffs.into_iter();
        let b_exps = other.exponents;
        let b_degs = other.total_degs;
        let mut b_coeffs = other.coeffs.into_iter();
        let (mut i, mut j) = (0usize, 0usize);
        while i < la && j < lb {
            let ae = &a_exps[i * n..(i + 1) * n];
            let be = &b_exps[j * n..(j + 1) * n];
            let ad = a_degs[i];
            let bd = b_degs[j];
            match Self::cmp_term_at(ae, ad, be, bd, ring.order) {
                Ordering::Greater => {
                    out_exps.extend_from_slice(ae);
                    out_coeffs.push(a_coeffs.next().unwrap());
                    out_degs.push(ad);
                    i += 1;
                }
                Ordering::Less => {
                    out_exps.extend_from_slice(be);
                    let bc = b_coeffs.next().unwrap();
                    out_coeffs.push(if negate_other { ring.field.neg_owned(bc) } else { bc });
                    out_degs.push(bd);
                    j += 1;
                }
                Ordering::Equal => {
                    let ac = a_coeffs.next().unwrap();
                    let bc = b_coeffs.next().unwrap();
                    let s = if negate_other { ring.field.sub_owned(ac, bc) } else { ring.field.add_owned(ac, bc) };
                    if !ring.field.is_zero(&s) {
                        out_exps.extend_from_slice(ae);
                        out_coeffs.push(s);
                        out_degs.push(ad);
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < la {
            let ae = &a_exps[i * n..(i + 1) * n];
            out_exps.extend_from_slice(ae);
            out_coeffs.push(a_coeffs.next().unwrap());
            out_degs.push(a_degs[i]);
            i += 1;
        }
        while j < lb {
            let be = &b_exps[j * n..(j + 1) * n];
            out_exps.extend_from_slice(be);
            let bc = b_coeffs.next().unwrap();
            out_coeffs.push(if negate_other { ring.field.neg_owned(bc) } else { bc });
            out_degs.push(b_degs[j]);
            j += 1;
        }
        DensePoly { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Merge-based subtraction.
    pub fn sub(&self, other: &DensePoly, ring: &PolyRing) -> DensePoly {
        self.merge_sorted(other, ring, true)
    }

    /// Multiply by a single (monomial, coefficient) term. Result preserves sorted order.
    pub fn mul_term(&self, term_exps: &[u16], term_coeff: &FieldElem, ring: &PolyRing) -> DensePoly {
        let n = ring.n_vars;
        debug_assert_eq!(term_exps.len(), n);
        if self.is_zero() || ring.field.is_zero(term_coeff) {
            return DensePoly::zero();
        }
        let term_deg: u32 = term_exps.iter().map(|&e| e as u32).sum();
        let mut out_exps: Vec<u16> = Vec::with_capacity(self.exponents.len());
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(self.coeffs.len());
        let mut out_degs: Vec<u32> = Vec::with_capacity(self.coeffs.len());
        for i in 0..self.coeffs.len() {
            let src = &self.exponents[i * n..(i + 1) * n];
            for k in 0..n {
                let sum = src[k].checked_add(term_exps[k])
                    .expect("exponent overflow: u16 too small for this polynomial degree");
                out_exps.push(sum);
            }
            out_coeffs.push(ring.field.mul(&self.coeffs[i], term_coeff));
            out_degs.push(self.total_degs[i] + term_deg);
        }
        DensePoly { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Schoolbook polynomial multiplication.
    pub fn mul(&self, other: &DensePoly, ring: &PolyRing) -> DensePoly {
        if self.is_zero() || other.is_zero() {
            return DensePoly::zero();
        }
        let n = ring.n_vars;
        // Accumulate as (Monomial, FieldElem) and let from_terms handle merge/sort.
        let mut acc: Vec<(Monomial, FieldElem)> =
            Vec::with_capacity(self.coeffs.len() * other.coeffs.len());
        for i in 0..self.coeffs.len() {
            let aexps = &self.exponents[i * n..(i + 1) * n];
            for j in 0..other.coeffs.len() {
                let bexps = &other.exponents[j * n..(j + 1) * n];
                let mut prod_exps = Vec::with_capacity(n);
                for k in 0..n {
                    prod_exps.push(aexps[k].checked_add(bexps[k])
                        .expect("exponent overflow: u16 too small for this polynomial degree"));
                }
                let prod_coeff = ring.field.mul(&self.coeffs[i], &other.coeffs[j]);
                acc.push((Monomial::from_exponents(prod_exps), prod_coeff));
            }
        }
        DensePoly::from_terms(acc, ring)
    }

    /// Evaluate at the given variable values.
    pub fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem {
        debug_assert_eq!(values.len(), ring.n_vars);
        if self.is_zero() {
            return ring.field.zero();
        }
        let n = ring.n_vars;
        let mut acc = ring.field.zero();
        for i in 0..self.coeffs.len() {
            let exps = &self.exponents[i * n..(i + 1) * n];
            let mut term_val = self.coeffs[i].clone();
            for v in 0..n {
                let e = exps[v];
                if e > 0 {
                    let p = ring.field.pow_u64(&values[v], e as u64);
                    ring.field.mul_assign(&mut term_val, &p);
                }
            }
            ring.field.add_assign(&mut acc, &term_val);
        }
        acc
    }

    /// Substitute `x_var <- value`.
    pub fn substitute_var(&self, var: usize, value: &FieldElem, ring: &PolyRing) -> DensePoly {
        if self.is_zero() {
            return DensePoly::zero();
        }
        let n = ring.n_vars;
        let mut acc: Vec<(Monomial, FieldElem)> = Vec::with_capacity(self.coeffs.len());
        for i in 0..self.coeffs.len() {
            let exps = &self.exponents[i * n..(i + 1) * n];
            let e = exps[var];
            let mut new_exps = exps.to_vec();
            new_exps[var] = 0;
            let mut new_coeff = self.coeffs[i].clone();
            if e > 0 {
                let p = ring.field.pow_u64(value, e as u64);
                ring.field.mul_assign(&mut new_coeff, &p);
            }
            if !ring.field.is_zero(&new_coeff) {
                acc.push((Monomial::from_exponents(new_exps), new_coeff));
            }
        }
        DensePoly::from_terms(acc, ring)
    }

    /// Returns `(var, max_exponent)` for each variable that appears with a nonzero exponent.
    pub fn appearing_variables(&self, ring: &PolyRing) -> Vec<(usize, u16)> {
        let n = ring.n_vars;
        let mut max_exp = vec![0u16; n];
        for i in 0..self.coeffs.len() {
            let exps = &self.exponents[i * n..(i + 1) * n];
            for v in 0..n {
                if exps[v] > max_exp[v] {
                    max_exp[v] = exps[v];
                }
            }
        }
        max_exp
            .into_iter()
            .enumerate()
            .filter(|(_, e)| *e > 0)
            .collect()
    }

    /// If this polynomial mentions only one variable, return its index.
    pub fn is_univariate(&self, ring: &PolyRing) -> Option<usize> {
        let appearing = self.appearing_variables(ring);
        if appearing.len() == 1 {
            Some(appearing[0].0)
        } else {
            None
        }
    }

    /// DensePoly division/remainder by a slice of divisors. Returns the normal form.
    ///
    /// Standard multivariate division: at each step, find a divisor whose leading
    /// monomial divides the leading monomial of the running remainder; subtract
    /// `(lc/lc_d) * (lt/lt_d) * d`. If no divisor matches the leading term, move
    /// it to the result and continue.
    pub fn reduce_by(&self, divisors: &[DensePoly], ring: &PolyRing) -> DensePoly {
        // Forward to the by-reference variant so callers that already hold
        // `&[DensePoly]` (e.g. `Ideal::reduce`) don't have to allocate a
        // ref vec themselves.
        let refs: Vec<&DensePoly> = divisors.iter().collect();
        self.reduce_by_refs(&refs, ring)
    }

    /// Fused merge of `self[cursor+1..]` with `divisor[1..] * (shift, neg_coeff)`.
    ///
    /// The leading terms cancel by construction (the divisor was chosen so that
    /// `LT(divisor) * shift == LT(self[cursor])`), so both are skipped.
    /// Only used by `reduce_by_refs_naive`, which is itself a cross-validation
    /// reference for the geobucket-based `reduce_by_refs`.
    ///
    /// `shift[k] = lt_exps[k] - d_lt_exps[k]` (the monomial multiplier).
    fn merge_sub_scaled_tail(
        &self,
        cursor: usize,
        divisor: &DensePoly,
        shift: &[u16],
        neg_coeff: &FieldElem,
        ring: &PolyRing,
    ) -> DensePoly {
        let n = ring.n_vars;
        let self_start = cursor + 1;
        let self_len = self.coeffs.len();
        let div_len = divisor.coeffs.len();
        // Divisor term 0 is the LT that cancels; iterate from term 1.
        let div_start = 1usize;

        let cap = (self_len - self_start) + (div_len - div_start);
        let mut out_exps: Vec<u16> = Vec::with_capacity(cap * n);
        let mut out_coeffs: Vec<FieldElem> = Vec::with_capacity(cap);
        let mut out_degs: Vec<u32> = Vec::with_capacity(cap);

        let shift_deg: u32 = shift.iter().map(|&e| e as u32).sum();

        let mut si = self_start;
        let mut di = div_start;

        // Temporary buffer for shifted divisor exponents (reused across iterations).
        let mut shifted = vec![0u16; n];

        while si < self_len && di < div_len {
            let se = &self.exponents[si * n..(si + 1) * n];
            let sd = self.total_degs[si];

            // Compute shifted divisor exponents inline.
            let de_base = &divisor.exponents[di * n..(di + 1) * n];
            let dd = divisor.total_degs[di] + shift_deg;
            for k in 0..n {
                shifted[k] = de_base[k]
                    .checked_add(shift[k])
                    .expect("exponent exceeds u16 in merge_sub_scaled_tail");
            }

            match Self::cmp_term_at(se, sd, &shifted, dd, ring.order) {
                Ordering::Greater => {
                    out_exps.extend_from_slice(se);
                    out_coeffs.push(self.coeffs[si].clone());
                    out_degs.push(sd);
                    si += 1;
                }
                Ordering::Less => {
                    out_exps.extend_from_slice(&shifted);
                    out_coeffs.push(ring.field.mul(&divisor.coeffs[di], neg_coeff));
                    out_degs.push(dd);
                    di += 1;
                }
                Ordering::Equal => {
                    // Same monomial — add coefficients (self + neg_coeff * divisor).
                    let dc = ring.field.mul(&divisor.coeffs[di], neg_coeff);
                    let s = ring.field.add(&self.coeffs[si], &dc);
                    if !ring.field.is_zero(&s) {
                        out_exps.extend_from_slice(se);
                        out_coeffs.push(s);
                        out_degs.push(sd);
                    }
                    si += 1;
                    di += 1;
                }
            }
        }

        // Drain remaining self terms.
        while si < self_len {
            let se = &self.exponents[si * n..(si + 1) * n];
            out_exps.extend_from_slice(se);
            out_coeffs.push(self.coeffs[si].clone());
            out_degs.push(self.total_degs[si]);
            si += 1;
        }

        // Drain remaining divisor terms (shifted + scaled).
        while di < div_len {
            let de_base = &divisor.exponents[di * n..(di + 1) * n];
            let dd = divisor.total_degs[di] + shift_deg;
            for k in 0..n {
                shifted[k] = de_base[k]
                    .checked_add(shift[k])
                    .expect("exponent exceeds u16 in merge_sub_scaled_tail");
            }
            out_exps.extend_from_slice(&shifted);
            out_coeffs.push(ring.field.mul(&divisor.coeffs[di], neg_coeff));
            out_degs.push(dd);
            di += 1;
        }

        DensePoly { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

}

mod dense_reduce;

impl super::repr::PolyRepr for DensePoly {
    type Mono = Monomial;

    fn zero() -> Self {
        DensePoly::zero()
    }
    fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        DensePoly::constant(c, ring)
    }
    fn variable(var: usize, ring: &PolyRing) -> Self {
        DensePoly::variable(var, ring)
    }
    fn from_terms(terms: Vec<(Monomial, FieldElem)>, ring: &PolyRing) -> Self {
        DensePoly::from_terms(terms, ring)
    }
    #[inline]
    fn is_zero(&self) -> bool {
        DensePoly::is_zero(self)
    }
    fn num_terms(&self) -> usize {
        DensePoly::num_terms(self)
    }
    fn add(&self, other: &Self, ring: &PolyRing) -> Self {
        DensePoly::add(self, other, ring)
    }
    fn sub(&self, other: &Self, ring: &PolyRing) -> Self {
        DensePoly::sub(self, other, ring)
    }
    fn mul(&self, other: &Self, ring: &PolyRing) -> Self {
        DensePoly::mul(self, other, ring)
    }
    fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Self {
        DensePoly::scale(self, c, ring)
    }
    fn negate(&self, ring: &PolyRing) -> Self {
        DensePoly::negate(self, ring)
    }
    fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem {
        DensePoly::evaluate(self, values, ring)
    }
    fn collect_terms_idx(&self, ring: &PolyRing) -> Vec<(num_bigint::BigUint, Vec<(usize, u16)>)> {
        self.terms(ring)
            .map(|t| {
                let coeff = ring.field.to_biguint(t.coefficient());
                let vars: Vec<(usize, u16)> = t
                    .exponents()
                    .iter()
                    .enumerate()
                    .filter(|&(_, &e)| e > 0)
                    .map(|(i, &e)| (i, e))
                    .collect();
                (coeff, vars)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests;
