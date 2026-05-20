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
}

impl PolyRing {
    pub fn new(field: PrimeField, var_names: Vec<String>, order: MonomialOrder) -> Arc<Self> {
        let n_vars = var_names.len();
        // Heuristic exponent cap: monomials beyond degree 16 in any
        // single variable are rare for the inputs the solver sees.
        let divmask = DivMaskScheme::build(n_vars, 16);
        Arc::new(PolyRing { field, n_vars, order, var_names, divmask })
    }

    pub fn with_divmask(
        field: PrimeField,
        var_names: Vec<String>,
        order: MonomialOrder,
        max_deg_hint: u16,
    ) -> Arc<Self> {
        let n_vars = var_names.len();
        let divmask = DivMaskScheme::build(n_vars, max_deg_hint);
        Arc::new(PolyRing { field, n_vars, order, var_names, divmask })
    }
}

/// A multivariate polynomial in flat storage.
#[derive(Clone, Debug)]
pub struct Polynomial {
    /// Flat exponent storage, length `num_terms * ring.n_vars`.
    exponents: Vec<u16>,
    /// Coefficients, length `num_terms`. All nonzero.
    coeffs: Vec<FieldElem>,
    /// Cached total degree per term (length `num_terms`).
    total_degs: Vec<u32>,
}

/// A lightweight reference to a single term within a polynomial.
#[derive(Copy, Clone, Debug)]
pub struct TermRef<'a> {
    poly: &'a Polynomial,
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

impl Polynomial {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Polynomial { exponents: Vec::new(), coeffs: Vec::new(), total_degs: Vec::new() }
    }

    /// Construct a constant polynomial. Returns the zero polynomial if `c` is zero.
    pub fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        if ring.field.is_zero(&c) {
            return Polynomial::zero();
        }
        Polynomial {
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
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
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
        debug_assert!(
            total_degs.windows(2).all(|w| w[0] >= w[1]),
            "from_raw_sorted: total_degs must be non-increasing (descending order)"
        );
        Polynomial { exponents, coeffs, total_degs }
    }

    /// `x_var` as a monomial polynomial with coefficient 1.
    pub fn variable(var: usize, ring: &PolyRing) -> Self {
        let mut exps = vec![0u16; ring.n_vars];
        exps[var] = 1;
        Polynomial {
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

    pub fn leading_coefficient(&self) -> Option<&FieldElem> {
        self.coeffs.first()
    }

    pub fn leading_monomial(&self, ring: &PolyRing) -> Option<Monomial> {
        self.leading_term(ring).map(|t| t.monomial())
    }

    /// Maximum total degree across all terms.
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
    pub(crate) fn raw_exponents(&self) -> &[u16] { &self.exponents }
    #[inline]
    pub(crate) fn raw_coeffs(&self) -> &[FieldElem] { &self.coeffs }
    #[inline]
    pub(crate) fn raw_total_degs(&self) -> &[u32] { &self.total_degs }

    /// Negate every coefficient in place.
    pub fn negate_in_place(&mut self, ring: &PolyRing) {
        for c in self.coeffs.iter_mut() {
            *c = ring.field.neg(c);
        }
    }

    pub fn negate(&self, ring: &PolyRing) -> Polynomial {
        let mut out = self.clone();
        out.negate_in_place(ring);
        out
    }

    /// Multiply every coefficient by `c`. Returns zero if `c == 0`.
    pub fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Polynomial {
        if ring.field.is_zero(c) {
            return Polynomial::zero();
        }
        if ring.field.is_one(c) {
            return self.clone();
        }
        let coeffs: Vec<FieldElem> = self.coeffs.iter().map(|x| ring.field.mul(x, c)).collect();
        Polynomial {
            exponents: self.exponents.clone(),
            coeffs,
            total_degs: self.total_degs.clone(),
        }
    }

    /// Make polynomial monic (divide by leading coefficient). No-op for zero.
    pub fn make_monic(&self, ring: &PolyRing) -> Polynomial {
        if self.is_zero() {
            return Polynomial::zero();
        }
        let lc = self.coeffs[0].clone();
        if ring.field.is_one(&lc) {
            return self.clone();
        }
        let lc_inv = ring.field.inv(&lc).expect("nonzero lc");
        self.scale(&lc_inv, ring)
    }

    /// Comparison helper between term `i` of `self` and term `j` of `other` under the ring order.
    pub(crate) fn cmp_term_at(
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
        }
    }

    fn merge_sorted(&self, other: &Polynomial, ring: &PolyRing, negate_other: bool) -> Polynomial {
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
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Merge-based addition. Both inputs are descending-sorted.
    pub fn add(&self, other: &Polynomial, ring: &PolyRing) -> Polynomial {
        self.merge_sorted(other, ring, false)
    }

    /// Move-based merge for cases where both inputs are owned. Recycles
    /// each input's `FieldElem` allocations into the output rather than
    /// cloning them, eliminating O(M + N) GMP `Integer` allocations
    /// per merge.
    pub fn merge_owned(self, other: Polynomial, ring: &PolyRing, negate_other: bool) -> Polynomial {
        if self.is_zero() {
            return if negate_other { other.negate(ring) } else { other };
        }
        if other.is_zero() {
            return self;
        }
        if crate::profile::gb_stats_enabled() {
            crate::profile::SPLIT_GB.merge_owned_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            crate::profile::SPLIT_GB.merge_owned_terms_total
                .fetch_add((self.coeffs.len() + other.coeffs.len()) as u64,
                    std::sync::atomic::Ordering::Relaxed);
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
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Merge-based subtraction.
    pub fn sub(&self, other: &Polynomial, ring: &PolyRing) -> Polynomial {
        self.merge_sorted(other, ring, true)
    }

    /// Multiply by a single (monomial, coefficient) term. Result preserves sorted order.
    pub fn mul_term(&self, term_exps: &[u16], term_coeff: &FieldElem, ring: &PolyRing) -> Polynomial {
        let n = ring.n_vars;
        debug_assert_eq!(term_exps.len(), n);
        if self.is_zero() || ring.field.is_zero(term_coeff) {
            return Polynomial::zero();
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
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Schoolbook polynomial multiplication.
    pub fn mul(&self, other: &Polynomial, ring: &PolyRing) -> Polynomial {
        if self.is_zero() || other.is_zero() {
            return Polynomial::zero();
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
        Polynomial::from_terms(acc, ring)
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
    pub fn substitute_var(&self, var: usize, value: &FieldElem, ring: &PolyRing) -> Polynomial {
        if self.is_zero() {
            return Polynomial::zero();
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
        Polynomial::from_terms(acc, ring)
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
        } else if appearing.is_empty() {
            None
        } else {
            None
        }
    }

    /// Polynomial division/remainder by a slice of divisors. Returns the normal form.
    ///
    /// Standard multivariate division: at each step, find a divisor whose leading
    /// monomial divides the leading monomial of the running remainder; subtract
    /// `(lc/lc_d) * (lt/lt_d) * d`. If no divisor matches the leading term, move
    /// it to the result and continue.
    pub fn reduce_by(&self, divisors: &[Polynomial], ring: &PolyRing) -> Polynomial {
        // Forward to the by-reference variant so callers that already hold
        // `&[Polynomial]` (e.g. `Ideal::reduce`) don't have to allocate a
        // ref vec themselves.
        let refs: Vec<&Polynomial> = divisors.iter().collect();
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
    #[cfg(test)]
    fn merge_sub_scaled_tail(
        &self,
        cursor: usize,
        divisor: &Polynomial,
        shift: &[u16],
        neg_coeff: &FieldElem,
        ring: &PolyRing,
    ) -> Polynomial {
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
                shifted[k] = de_base[k] + shift[k];
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
                shifted[k] = de_base[k] + shift[k];
            }
            out_exps.extend_from_slice(&shifted);
            out_coeffs.push(ring.field.mul(&divisor.coeffs[di], neg_coeff));
            out_degs.push(dd);
            di += 1;
        }

        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Like `reduce_by` but takes references to divisors — avoids cloning
    /// the divisor list when the caller already holds polynomials inside
    /// some larger container (e.g. `BuchbergerState::basis`).
    ///
    /// Geobucket-based accumulator (Yan 1998). Each reduction step is
    /// O(D · log(N / D)) where D is the divisor length and N is the
    /// running tail size.
    pub fn reduce_by_refs(&self, divisors: &[&Polynomial], ring: &PolyRing) -> Polynomial {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, None)
    }

    /// Cancel-aware variant of [`reduce_by_refs`]. On cancel, returns
    /// the partial remainder accumulated so far — sound (same residue
    /// class) but not necessarily a normal form. Hot paths (Buchberger
    /// main loop, interreduce, bit-prop `contains`) should prefer this
    /// over [`reduce_by_refs`] so the cancel token is honoured on
    /// dense polynomials.
    pub fn reduce_by_refs_cancel(
        &self,
        divisors: &[&Polynomial],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
    ) -> Polynomial {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, Some(cancel), None)
    }

    /// Variant of [`reduce_by_refs_cancel`] that also records, in
    /// `use_counts`, how many times each divisor was selected as the
    /// reducer during this call. `use_counts.len()` must equal
    /// `divisors.len()`; entries are incremented (not zeroed).
    pub fn reduce_by_refs_counted_cancel(
        &self,
        divisors: &[&Polynomial],
        ring: &PolyRing,
        cancel: &crate::timeout::CancelToken,
        use_counts: &mut [u64],
    ) -> Polynomial {
        debug_assert_eq!(divisors.len(), use_counts.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, Some(cancel), Some(use_counts))
    }

    /// Non-cancel-aware version of [`reduce_by_refs_counted_cancel`].
    pub fn reduce_by_refs_counted(
        &self,
        divisors: &[&Polynomial],
        ring: &PolyRing,
        use_counts: &mut [u64],
    ) -> Polynomial {
        debug_assert_eq!(divisors.len(), use_counts.len());
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        self.reduce_by_refs_geobucket(divisors, ring, None, Some(use_counts))
    }

    /// Geobucket-based reduction. Public for testing — production code should
    /// go through `reduce_by_refs` so the dispatch (currently always geobucket)
    /// stays in one place.
    ///
    /// When `use_counts` is provided, the per-divisor counter at the
    /// index of the selected reducer is incremented every iteration.
    pub(crate) fn reduce_by_refs_geobucket(
        &self,
        divisors: &[&Polynomial],
        ring: &PolyRing,
        cancel: Option<&crate::timeout::CancelToken>,
        mut use_counts: Option<&mut [u64]>,
    ) -> Polynomial {
        let n = ring.n_vars;
        let stats_on = crate::profile::gb_stats_enabled();
        if stats_on {
            crate::profile::SPLIT_GB.reduce_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let setup_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };

        // Precompute LT info for each divisor. The exponent slice is
        // BORROWED rather than cloned, saving an O(n_vars) Vec allocation
        // per divisor.
        use super::divmask::DivMask;
        let div_lt: Vec<Option<(&[u16], u32, FieldElem, DivMask)>> = divisors
            .iter()
            .map(|d| {
                if let Some(lt) = d.leading_term(ring) {
                    let exps = lt.exponents();  // borrows from divisor
                    let total_deg = lt.total_degree();
                    let dm = ring.divmask.compute_from_slice(exps);
                    Some((exps, total_deg, lt.coefficient().clone(), dm))
                } else {
                    None
                }
            })
            .collect();
        // When the divisor set is large, build an auxiliary index
        // sorted by leading-term total degree ascending. The lookup
        // loop iterates this index and `break`s on the first divisor
        // whose LT degree exceeds `lt_deg`. The normal-form output is
        // unchanged because the first divisor whose LT divides
        // `lt_exps` is unique on a Groebner-basis-shaped divisor set;
        // for small divisor sets the linear scan path is kept so
        // unit-tests' "reducer matches naive" property is preserved.
        const SORT_THRESHOLD: usize = 64;
        let order_opt: Option<Vec<usize>> = if div_lt.len() >= SORT_THRESHOLD {
            let mut order: Vec<usize> = (0..div_lt.len()).collect();
            order.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
            Some(order)
        } else {
            None
        };

        // Hash-bucketed divisor index, keyed on `DivMask`. Only enabled
        // at ≥ 256 divisors, where `DivMask` filtering wins over the
        // sort + early-break path; below this threshold the cost of
        // building / iterating the buckets outweighs the savings.
        const BUCKET_THRESHOLD: usize = 256;
        let bucket_index_opt: Option<std::collections::HashMap<u128, Vec<usize>>> =
            if div_lt.len() >= BUCKET_THRESHOLD {
                let mut buckets: std::collections::HashMap<u128, Vec<usize>> =
                    std::collections::HashMap::new();
                for (i, lt_opt) in div_lt.iter().enumerate() {
                    if let Some((_, _, _, dm)) = lt_opt {
                        buckets.entry(dm.0).or_default().push(i);
                    }
                }
                // Sort each bucket by leading-term total degree
                // ascending so the lookup loop can `break` (not
                // `continue`) on the first divisor with deg > lt_deg.
                for indices in buckets.values_mut() {
                    indices.sort_by_key(|&i| div_lt[i].as_ref().map(|t| t.1).unwrap_or(u32::MAX));
                }
                Some(buckets)
            } else {
                None
            };

        let mut gb = super::geobucket::Geobucket::from_poly(self.clone(), ring);
        let mut result_exps: Vec<u16> = Vec::new();
        let mut result_coeffs: Vec<FieldElem> = Vec::new();
        let mut result_degs: Vec<u32> = Vec::new();
        let mut shift = vec![0u16; n];

        if let Some(t0) = setup_t0 {
            crate::profile::SPLIT_GB.time_div_lt_setup_ns
                .fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        let mut local_pops: u64 = 0;
        let mut local_lookups: u64 = 0;
        let mut local_sub_scaled: u64 = 0;
        let mut local_pop_ns: u64 = 0;
        let mut local_lookup_ns: u64 = 0;
        let mut local_sub_ns: u64 = 0;

        // Throttle the cancel check coarsely. Checking the atomic on
        // every iteration measurably slows reduction; period = 4096
        // keeps the per-iteration overhead unmeasurable while still
        // bounding cancel latency at the millisecond scale.
        let mut iter_counter: u32 = 0;
        const CANCEL_CHECK_PERIOD: u32 = 4096;
        // Bind the cancel reference outside the loop so the per-iteration
        // path doesn't re-pattern-match the Option.
        let cancel_ref = cancel;
        loop {
            let pop_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let popped = gb.pop_leading_term();
            if let Some(t0) = pop_t0 {
                local_pop_ns += t0.elapsed().as_nanos() as u64;
            }
            let (lt_exps, lt_deg, lt_coeff) = match popped {
                Some(t) => t,
                None => break,
            };
            local_pops += 1;
            iter_counter = iter_counter.wrapping_add(1);
            if iter_counter & (CANCEL_CHECK_PERIOD - 1) == 0 {
                if let Some(c) = cancel_ref {
                    if c.is_cancelled() {
                        while let Some((e, d, c2)) = gb.pop_leading_term() {
                            result_exps.extend_from_slice(&e);
                            result_coeffs.push(c2);
                            result_degs.push(d);
                        }
                        if stats_on {
                            let g = &crate::profile::SPLIT_GB;
                            g.reduce_lt_pops.fetch_add(local_pops, std::sync::atomic::Ordering::Relaxed);
                            g.reduce_div_lookups.fetch_add(local_lookups, std::sync::atomic::Ordering::Relaxed);
                            g.reduce_sub_scaled_calls.fetch_add(local_sub_scaled, std::sync::atomic::Ordering::Relaxed);
                            g.time_pop_lt_ns.fetch_add(local_pop_ns, std::sync::atomic::Ordering::Relaxed);
                            g.time_div_lookup_ns.fetch_add(local_lookup_ns, std::sync::atomic::Ordering::Relaxed);
                            g.time_sub_scaled_ns.fetch_add(local_sub_ns, std::sync::atomic::Ordering::Relaxed);
                        }
                        return Polynomial::from_raw_sorted(result_exps, result_coeffs, result_degs);
                    }
                }
            }
            let lookup_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let cur_dm = ring.divmask.compute_from_slice(&lt_exps);
            let mut chosen: Option<usize> = None;
            if let Some(buckets) = &bucket_index_opt {
                // Hash-bucketed divisor lookup. Iterate only buckets
                // whose mask is a submask of `cur_dm` — others contain
                // divisors whose `DivMask` has bits `cur_dm` does not,
                // so they cannot divide. Within a compatible bucket
                // perform the full exponent check; break on the first
                // match. The pick is process-deterministic but may
                // differ from the linear-scan first-match across runs.
                let cur_bits = cur_dm.0;
                'outer: for (&mask, indices) in buckets {
                    if (mask & !cur_bits) != 0 {
                        // mask has bits cur_dm doesn't → no divisor in
                        // this bucket can divide LT.
                        continue;
                    }
                    for &di in indices {
                        local_lookups += 1;
                        if let Some((d_exps, d_deg, _, _)) = &div_lt[di] {
                            if *d_deg > lt_deg {
                                // Bucket is sorted by LT degree ascending;
                                // once it exceeds `lt_deg`, every later
                                // divisor in this bucket is also too big.
                                break;
                            }
                            let mut divides = true;
                            for k in 0..n {
                                if d_exps[k] > lt_exps[k] {
                                    divides = false;
                                    break;
                                }
                            }
                            if divides {
                                chosen = Some(di);
                                break 'outer;
                            }
                        }
                    }
                }
            } else if let Some(order) = &order_opt {
                // Sorted-ascending iteration with early break on
                // exceeded-degree divisors.
                for &di in order {
                    local_lookups += 1;
                    if let Some((d_exps, d_deg, _, d_dm)) = &div_lt[di] {
                        if *d_deg > lt_deg {
                            break;
                        }
                        if !d_dm.divides_consistent_with(cur_dm) {
                            continue;
                        }
                        let mut divides = true;
                        for k in 0..n {
                            if d_exps[k] > lt_exps[k] {
                                divides = false;
                                break;
                            }
                        }
                        if divides {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            } else {
                for (di, lt_opt) in div_lt.iter().enumerate() {
                    local_lookups += 1;
                    if let Some((d_exps, d_deg, _, d_dm)) = lt_opt {
                        if *d_deg > lt_deg {
                            continue;
                        }
                        if !d_dm.divides_consistent_with(cur_dm) {
                            continue;
                        }
                        let mut divides = true;
                        for k in 0..n {
                            if d_exps[k] > lt_exps[k] {
                                divides = false;
                                break;
                            }
                        }
                        if divides {
                            chosen = Some(di);
                            break;
                        }
                    }
                }
            }
            if let Some(t0) = lookup_t0 {
                local_lookup_ns += t0.elapsed().as_nanos() as u64;
            }

            if let Some(di) = chosen {
                let sub_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
                let (d_exps, _d_deg, d_lc, _) = div_lt[di].as_ref().unwrap();
                let coeff_ratio = ring.field.div(&lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                for k in 0..n {
                    shift[k] = lt_exps[k] - d_exps[k];
                }
                gb.sub_scaled_tail(&shift, &neg_coeff, divisors[di]);
                local_sub_scaled += 1;
                if let Some(counts) = use_counts.as_deref_mut() {
                    counts[di] = counts[di].saturating_add(1);
                }
                if let Some(t0) = sub_t0 {
                    local_sub_ns += t0.elapsed().as_nanos() as u64;
                }
            } else {
                result_exps.extend_from_slice(&lt_exps);
                result_coeffs.push(lt_coeff);
                result_degs.push(lt_deg);
            }
        }

        let fin_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
        let result = Polynomial::from_raw_sorted(result_exps, result_coeffs, result_degs);
        if let Some(t0) = fin_t0 {
            crate::profile::SPLIT_GB.time_finalize_ns
                .fetch_add(t0.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
        }
        if stats_on {
            let g = &crate::profile::SPLIT_GB;
            g.reduce_lt_pops.fetch_add(local_pops, std::sync::atomic::Ordering::Relaxed);
            g.reduce_div_lookups.fetch_add(local_lookups, std::sync::atomic::Ordering::Relaxed);
            g.reduce_sub_scaled_calls.fetch_add(local_sub_scaled, std::sync::atomic::Ordering::Relaxed);
            g.time_pop_lt_ns.fetch_add(local_pop_ns, std::sync::atomic::Ordering::Relaxed);
            g.time_div_lookup_ns.fetch_add(local_lookup_ns, std::sync::atomic::Ordering::Relaxed);
            g.time_sub_scaled_ns.fetch_add(local_sub_ns, std::sync::atomic::Ordering::Relaxed);
        }
        result
    }

    /// Single-vector reduction with fused `merge_sub_scaled_tail`. Retained
    /// as the cross-validation reference for the geobucket-based
    /// `reduce_by_refs`; only compiled under `cfg(test)`.
    #[cfg(test)]
    pub(crate) fn reduce_by_refs_naive(&self, divisors: &[&Polynomial], ring: &PolyRing) -> Polynomial {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        let n = ring.n_vars;
        let mut current = self.clone();
        let mut cursor: usize = 0;
        let mut result_exps: Vec<u16> = Vec::new();
        let mut result_coeffs: Vec<FieldElem> = Vec::new();
        let mut result_degs: Vec<u32> = Vec::new();

        use super::divmask::DivMask;
        let div_lt: Vec<Option<(Vec<u16>, u32, FieldElem, DivMask)>> = divisors
            .iter()
            .map(|d| {
                if let Some(lt) = d.leading_term(ring) {
                    let mon = lt.monomial();
                    let dm = ring.divmask.compute(&mon);
                    Some((lt.exponents().to_vec(), lt.total_degree(), lt.coefficient().clone(), dm))
                } else {
                    None
                }
            })
            .collect();

        while cursor < current.coeffs.len() {
            let lt_exps: &[u16] = &current.exponents[cursor * n..(cursor + 1) * n];
            let lt_deg = current.total_degs[cursor];
            let cur_dm = ring.divmask.compute_from_slice(lt_exps);

            let mut chosen: Option<usize> = None;
            for (di, lt_opt) in div_lt.iter().enumerate() {
                if let Some((d_exps, d_deg, _, d_dm)) = lt_opt {
                    if *d_deg > lt_deg {
                        continue;
                    }
                    if !d_dm.divides_consistent_with(cur_dm) {
                        continue;
                    }
                    let mut divides = true;
                    for k in 0..n {
                        if d_exps[k] > lt_exps[k] {
                            divides = false;
                            break;
                        }
                    }
                    if divides {
                        chosen = Some(di);
                        break;
                    }
                }
            }

            if let Some(di) = chosen {
                let (d_exps, _d_deg, d_lc, _) = div_lt[di].as_ref().unwrap();
                let lt_coeff = &current.coeffs[cursor];
                let coeff_ratio = ring.field.div(lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                let mut shift = vec![0u16; n];
                for k in 0..n {
                    shift[k] = lt_exps[k] - d_exps[k];
                }
                current = current.merge_sub_scaled_tail(
                    cursor, divisors[di], &shift, &neg_coeff, ring,
                );
                cursor = 0;
            } else {
                result_exps.extend_from_slice(&current.exponents[cursor * n..(cursor + 1) * n]);
                result_coeffs.push(current.coeffs[cursor].clone());
                result_degs.push(current.total_degs[cursor]);
                cursor += 1;
            }
        }

        Polynomial::from_raw_sorted(result_exps, result_coeffs, result_degs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn small_ring() -> Arc<PolyRing> {
        let f = PrimeField::new(BigUint::from(101u32));
        PolyRing::new(f, vec!["x".into(), "y".into(), "z".into()], MonomialOrder::DegRevLex)
    }

    #[test]
    fn from_terms_sorts_and_dedupes() {
        let r = small_ring();
        let f = &r.field;
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(5)),
                (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(3)),
                (Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(4)), // should sum
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(2)),
            ],
            &r,
        );
        // After dedup: [(2,1,0)*7, (1,0,0)*2, (0,0,0)*5] (descending DegRevLex)
        assert_eq!(p.num_terms(), 3);
        let lt = p.leading_term(&r).unwrap();
        assert_eq!(lt.exponents(), &[2, 1, 0]);
        assert_eq!(*lt.coefficient(), f.from_u64(7));
    }

    #[test]
    fn add_sub_cancellation() {
        let r = small_ring();
        let f = &r.field;
        let a = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(3)),
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_u64(5)),
            ],
            &r,
        );
        let b = a.clone();
        let zero = a.sub(&b, &r);
        assert!(zero.is_zero());
        let two_a = a.add(&a, &r);
        assert_eq!(two_a.num_terms(), 2);
        assert_eq!(*two_a.leading_term(&r).unwrap().coefficient(), f.from_u64(6));
    }

    #[test]
    fn mul_works() {
        let r = small_ring();
        let f = &r.field;
        // (x + 1)(x - 1) = x^2 - 1
        let a = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(1)),
            ],
            &r,
        );
        let b = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        let prod = a.mul(&b, &r);
        // x^2 - 1
        assert_eq!(prod.num_terms(), 2);
        let terms: Vec<_> = prod.terms(&r).collect();
        assert_eq!(terms[0].exponents(), &[2, 0, 0]);
        assert_eq!(*terms[0].coefficient(), f.from_u64(1));
        assert_eq!(terms[1].exponents(), &[0, 0, 0]);
        assert_eq!(*terms[1].coefficient(), f.from_i64(-1));
    }

    #[test]
    fn reduce_by_simple() {
        let r = small_ring();
        let f = &r.field;
        // Divide x^2*y by (x*y - 1) over GF(101) DegRevLex.
        // Quotient: x; remainder: x.
        let f1 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        let g = Polynomial::from_terms(
            vec![(Monomial::from_exponents(vec![2, 1, 0]), f.from_u64(1))],
            &r,
        );
        let nf = g.reduce_by(&[f1.clone()], &r);
        // x^2*y mod (x*y - 1): subtract x * (x*y - 1) = x^2*y - x => remainder x
        assert_eq!(nf.num_terms(), 1);
        let lt = nf.leading_term(&r).unwrap();
        assert_eq!(lt.exponents(), &[1, 0, 0]);
        assert_eq!(*lt.coefficient(), f.from_u64(1));
    }

    #[test]
    fn reduce_by_refs_geobucket_matches_naive() {
        // Build a non-trivial reduction: a polynomial with multiple terms
        // reducible by several divisors, requiring many reduction steps.
        let r = small_ring();
        let f = &r.field;
        // Divisors: x^3 - 2*y, x*y - z, y^2 - 1
        let d1 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_i64(-2)),
            ],
            &r,
        );
        let d2 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 1]), f.from_i64(-1)),
            ],
            &r,
        );
        let d3 = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![0, 2, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        // Subject: x^4*y^2 + 5*x^3*y + 7*x*y^2 + z + 11
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![4, 2, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![3, 1, 0]), f.from_u64(5)),
                (Monomial::from_exponents(vec![1, 2, 0]), f.from_u64(7)),
                (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(11)),
            ],
            &r,
        );
        let divs: Vec<&Polynomial> = vec![&d1, &d2, &d3];
        let geo = p.reduce_by_refs_geobucket(&divs, &r, None, None);
        let naive = p.reduce_by_refs_naive(&divs, &r);
        let dispatched = p.reduce_by_refs(&divs, &r);
        assert_eq!(geo.num_terms(), naive.num_terms());
        assert_eq!(dispatched.num_terms(), naive.num_terms());
        for (a, b) in geo.terms(&r).zip(naive.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
        for (a, b) in dispatched.terms(&r).zip(naive.terms(&r)) {
            assert_eq!(a.exponents(), b.exponents());
            assert_eq!(a.coefficient(), b.coefficient());
        }
    }

    #[test]
    fn reduce_by_refs_geobucket_to_zero() {
        // Polynomial that fully reduces to zero — exercises the cancellation
        // path in pop_leading_term across many steps.
        let r = small_ring();
        let f = &r.field;
        let d = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 1, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        // p = (x - y) * (x^2 + x*y + y^2) = x^3 - y^3
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![3, 0, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 3, 0]), f.from_i64(-1)),
            ],
            &r,
        );
        // p reduced by (x - y): leading reductions cancel until 0.
        let nf = p.reduce_by_refs_geobucket(&[&d], &r, None, None);
        let nf_naive = p.reduce_by_refs_naive(&[&d], &r);
        assert!(nf.is_zero(), "geobucket reduction should yield zero");
        assert!(nf_naive.is_zero(), "naive reduction should also yield zero");
    }

    #[test]
    fn evaluate_and_substitute() {
        let r = small_ring();
        let f = &r.field;
        // p = x*y + 2*z + 3
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 1, 0]), f.from_u64(1)),
                (Monomial::from_exponents(vec![0, 0, 1]), f.from_u64(2)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(3)),
            ],
            &r,
        );
        // p(2,3,4) = 6 + 8 + 3 = 17
        let v = vec![f.from_u64(2), f.from_u64(3), f.from_u64(4)];
        assert_eq!(p.evaluate(&v, &r), f.from_u64(17));
        // substitute z=4: p' = x*y + 11
        let q = p.substitute_var(2, &f.from_u64(4), &r);
        assert_eq!(q.num_terms(), 2);
    }

    #[test]
    fn make_monic_works() {
        let r = small_ring();
        let f = &r.field;
        let p = Polynomial::from_terms(
            vec![
                (Monomial::from_exponents(vec![1, 0, 0]), f.from_u64(7)),
                (Monomial::from_exponents(vec![0, 0, 0]), f.from_u64(14)),
            ],
            &r,
        );
        let m = p.make_monic(&r);
        assert!(f.is_one(m.leading_coefficient().unwrap()));
        // 14/7 = 2
        let const_term = m.terms(&r).last().unwrap();
        assert_eq!(*const_term.coefficient(), f.from_u64(2));
    }
}
