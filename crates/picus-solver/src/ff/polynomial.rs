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
        // Heuristic: budget for typical KPI workloads — exponents rarely exceed 16.
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
    pub fn coefficient(&self) -> &FieldElem {
        &self.poly.coeffs[self.idx]
    }

    #[inline]
    pub fn total_degree(&self) -> u32 {
        self.poly.total_degs[self.idx]
    }

    #[inline]
    pub fn exponents(&self) -> &[u16] {
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

    pub fn is_constant(&self, _ring: &PolyRing) -> bool {
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
        self.total_degs.iter().copied().max().unwrap_or(0)
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

    /// Produce a clone (alias for `Clone::clone` for API symmetry).
    pub fn clone_poly(&self) -> Self {
        self.clone()
    }

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
    fn cmp_term_at(
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

    /// Merge-based addition. Both inputs are descending-sorted.
    pub fn add(&self, other: &Polynomial, ring: &PolyRing) -> Polynomial {
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
                    out_coeffs.push(other.coeffs[j].clone());
                    out_degs.push(bd);
                    j += 1;
                }
                Ordering::Equal => {
                    let s = ring.field.add(&self.coeffs[i], &other.coeffs[j]);
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
            out_coeffs.push(other.coeffs[j].clone());
            out_degs.push(other.total_degs[j]);
            j += 1;
        }
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
    }

    /// Merge-based subtraction.
    pub fn sub(&self, other: &Polynomial, ring: &PolyRing) -> Polynomial {
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
                    out_coeffs.push(ring.field.neg(&other.coeffs[j]));
                    out_degs.push(bd);
                    j += 1;
                }
                Ordering::Equal => {
                    let s = ring.field.sub(&self.coeffs[i], &other.coeffs[j]);
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
            out_coeffs.push(ring.field.neg(&other.coeffs[j]));
            out_degs.push(other.total_degs[j]);
            j += 1;
        }
        Polynomial { exponents: out_exps, coeffs: out_coeffs, total_degs: out_degs }
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
                out_exps.push(src[k] + term_exps[k]);
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
                    prod_exps.push(aexps[k] + bexps[k]);
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

    /// Like `reduce_by` but takes references to divisors — avoids cloning
    /// the divisor list when the caller already holds polynomials inside
    /// some larger container (e.g. `BuchbergerState::basis`).
    pub fn reduce_by_refs(&self, divisors: &[&Polynomial], ring: &PolyRing) -> Polynomial {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        let n = ring.n_vars;
        let mut current = self.clone();
        let mut result_terms: Vec<(Monomial, FieldElem)> = Vec::new();

        // Precompute leading exponents/coeffs for divisors.
        let div_lt: Vec<Option<(Vec<u16>, u32, FieldElem)>> = divisors
            .iter()
            .map(|d| {
                if let Some(lt) = d.leading_term(ring) {
                    Some((lt.exponents().to_vec(), lt.total_degree(), lt.coefficient().clone()))
                } else {
                    None
                }
            })
            .collect();

        while !current.is_zero() {
            // Identify the leading term of `current` (slice, no copy).
            let lt_exps: &[u16] = &current.exponents[0..n];
            let lt_deg = current.total_degs[0];

            // Find a divisor whose LM divides current's LM.
            let mut chosen: Option<usize> = None;
            for (di, lt_opt) in div_lt.iter().enumerate() {
                if let Some((d_exps, d_deg, _)) = lt_opt {
                    if *d_deg > lt_deg {
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
                let (d_exps, _d_deg, d_lc) = div_lt[di].as_ref().unwrap();
                let lt_coeff = current.coeffs[0].clone();
                // Compute the multiplier term: (lc / d_lc) * (lt / d_lt).
                let coeff_ratio = ring.field.div(&lt_coeff, d_lc).expect("nonzero divisor LC");
                let neg_coeff = ring.field.neg(&coeff_ratio);
                let mut mul_exps = vec![0u16; n];
                for k in 0..n {
                    mul_exps[k] = lt_exps[k] - d_exps[k];
                }
                // current -= (coeff_ratio * (lt/d_lt)) * divisors[di]
                // i.e.    += (-coeff_ratio * (lt/d_lt)) * divisors[di]
                let scaled = divisors[di].mul_term(&mul_exps, &neg_coeff, ring);
                current = current.add(&scaled, ring);
            } else {
                // No reducer — peel off the leading term to result.
                let lt_exps_vec: Vec<u16> = current.exponents[0..n].to_vec();
                let lt_coeff = current.coeffs[0].clone();
                result_terms.push((Monomial::from_exponents(lt_exps_vec), lt_coeff));
                // Drop the leading term in-place.
                current.exponents.drain(0..n);
                current.coeffs.remove(0);
                current.total_degs.remove(0);
            }
        }

        Polynomial::from_terms(result_terms, ring)
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
