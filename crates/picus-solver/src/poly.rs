//! Multivariate polynomial ring over GF(p), backed by [`crate::ff`].
//!
//! Public surface: `FfPolyRing`, `Poly`, `Mono`, `pr.var(i)`,
//! `pr.constant(el)`, `pr.add/sub/mul/...`, and the inner `pr.ring.terms(&p)`
//! / `pr.ring.create_term(c, m)` / `pr.ring.exponent_at(m, i)` /
//! `pr.ring.appearing_indeterminates(&p)` / `pr.ring.indeterminate(i)`.
//! Storage and arithmetic are delegated to the [`crate::ff`] types.

use std::sync::Arc;

use crate::field::{FfEl, FfField};
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{PolyRing as FfPolyRingCtx, Polynomial};

/// Re-export the polynomial type for the rest of the crate.
pub type Poly = Polynomial;
/// Re-export the monomial type.
pub type Mono = Monomial;
/// Type alias for the polynomial-ring facade. `&PolyRingType` is the
/// reference shape used throughout picus-solver.
pub type PolyRingType = PolyRingFacade;

/// A multivariate polynomial ring GF(p)[x_0, ..., x_{n-1}].
///
/// `pr.ring` is a thin facade around the underlying [`ff::PolyRing`]
/// context, exposing `terms`, `create_term`, `exponent_at`, etc.
pub struct FfPolyRing {
    pub field: FfField,
    pub ring: PolyRingFacade,
    pub n_vars: usize,
    pub var_names: Vec<String>,
}

impl FfPolyRing {
    /// Create a new polynomial ring with degrevlex term order.
    pub fn new(field: FfField, var_names: Vec<String>) -> Self {
        let n_vars = var_names.len();
        let ctx = FfPolyRingCtx::new(
            field.clone(),
            var_names.clone(),
            MonomialOrder::DegRevLex,
        );
        let ring = PolyRingFacade { ctx };
        FfPolyRing { field, ring, n_vars, var_names }
    }

    /// i-th indeterminate as a polynomial.
    pub fn var(&self, index: usize) -> Poly {
        Polynomial::variable(index, &self.ring.ctx)
    }

    /// Constant polynomial from a field element.
    pub fn constant(&self, el: FfEl) -> Poly {
        Polynomial::constant(el, &self.ring.ctx)
    }

    pub fn zero(&self) -> Poly { Polynomial::zero() }
    pub fn one(&self) -> Poly { Polynomial::constant(self.field.one(), &self.ring.ctx) }

    pub fn add(&self, a: Poly, b: Poly) -> Poly { a.add(&b, &self.ring.ctx) }
    pub fn sub(&self, a: Poly, b: Poly) -> Poly { a.sub(&b, &self.ring.ctx) }
    pub fn mul(&self, a: Poly, b: Poly) -> Poly { a.mul(&b, &self.ring.ctx) }
    pub fn neg(&self, a: Poly) -> Poly { a.negate(&self.ring.ctx) }
    pub fn clone_poly(&self, p: &Poly) -> Poly { p.clone() }
    pub fn is_zero(&self, p: &Poly) -> bool { p.is_zero() }

    /// Multiply polynomial by a scalar.
    pub fn scale(&self, coeff: FfEl, poly: Poly) -> Poly {
        poly.scale(&coeff, &self.ring.ctx)
    }

    /// Look up variable index by name.
    pub fn var_index(&self, name: &str) -> Option<usize> {
        self.var_names.iter().position(|n| n == name)
    }

    /// Reference to the underlying `ff::PolyRing` context.
    pub fn ctx(&self) -> &Arc<FfPolyRingCtx> { &self.ring.ctx }
}

/// Facade exposing the `.ring.` method surface used throughout
/// picus-solver. Holds a shared `Arc<ff::PolyRing>` context and
/// dispatches to the appropriate `Polynomial` / `Monomial` methods.
pub struct PolyRingFacade {
    pub ctx: Arc<FfPolyRingCtx>,
}

impl PolyRingFacade {
    pub fn n_vars(&self) -> usize { self.ctx.n_vars }
    pub fn indeterminate_count(&self) -> usize { self.ctx.n_vars }

    pub fn var_names(&self) -> &[String] { &self.ctx.var_names }

    pub fn base_ring(&self) -> &crate::ff::field::PrimeField { &self.ctx.field }

    pub fn field(&self) -> &crate::ff::field::PrimeField { &self.ctx.field }

    /// Build a polynomial holding a single term `coeff * monomial`.
    pub fn create_term(&self, coeff: FfEl, mono: Monomial) -> Poly {
        Polynomial::from_terms(vec![(mono, coeff)], &self.ctx)
    }

    /// Build a polynomial from an iterator of `(coeff, monomial)` pairs.
    /// The resulting polynomial is canonicalised (terms summed/sorted).
    pub fn from_terms<I>(&self, terms: I) -> Poly
    where I: IntoIterator<Item = (FfEl, Monomial)>,
    {
        let v: Vec<(Monomial, FfEl)> = terms.into_iter().map(|(c, m)| (m, c)).collect();
        Polynomial::from_terms(v, &self.ctx)
    }

    /// Single-variable monomial of degree 1.
    pub fn indeterminate(&self, index: usize) -> Monomial {
        let mut e = vec![0u16; self.ctx.n_vars];
        e[index] = 1;
        Monomial::from_exponents(e)
    }

    /// Build a monomial from an exponent slice. Exponents are cast from
    /// `usize` down to `u16`.
    pub fn create_monomial(&self, exps: impl IntoIterator<Item = usize>) -> Monomial {
        Monomial::from_exponents(exps.into_iter().map(|e| e as u16).collect())
    }

    /// Iterator over the terms of `p` in descending order, yielding
    /// `(coefficient, monomial)` pairs. The monomial is freshly cloned per
    /// term (cheap; a small `Vec<u16>`).
    pub fn terms<'a>(&'a self, p: &'a Poly) -> TermsIter<'a> {
        TermsIter { poly: p, ctx: &self.ctx, idx: 0 }
    }

    /// Exponent of variable `var` in monomial `m`. Accepts both `&Monomial`
    /// and `Monomial` so callers iterating over [`Self::terms`], which
    /// yields owned `Monomial`s, can pass the value directly.
    pub fn exponent_at<M: std::borrow::Borrow<Monomial>>(&self, m: M, var: usize) -> usize {
        m.borrow().exponent(var) as usize
    }

    /// Clone a monomial. Accepts either `&Monomial` or `Monomial`.
    pub fn clone_monomial<M: std::borrow::Borrow<Monomial>>(&self, m: M) -> Monomial {
        m.borrow().clone()
    }

    /// Variables that actually appear in `p`, in ascending index order.
    /// Returned as an `AppearingVars` newtype supporting `.is_empty()`,
    /// iteration over variable indices, and indexed `(index, max_degree)`
    /// access.
    pub fn appearing_indeterminates(&self, p: &Poly) -> AppearingVars {
        AppearingVars { vars: p.appearing_variables(&self.ctx) }
    }

    /// Coefficient of `m` inside `p`. Linear scan (used rarely; performance
    /// non-critical).
    pub fn coefficient_at(&self, p: &Poly, m: &Monomial) -> FfEl {
        for t in p.terms(&self.ctx) {
            if t.monomial() == *m {
                return self.ctx.field.clone_el(t.coefficient());
            }
        }
        self.ctx.field.zero()
    }

    pub fn add(&self, a: Poly, b: Poly) -> Poly { a.add(&b, &self.ctx) }
    pub fn sub(&self, a: Poly, b: Poly) -> Poly { a.sub(&b, &self.ctx) }
    pub fn mul(&self, a: Poly, b: Poly) -> Poly { a.mul(&b, &self.ctx) }
    pub fn negate(&self, a: Poly) -> Poly { a.negate(&self.ctx) }
    pub fn clone_el(&self, p: &Poly) -> Poly { p.clone() }
    pub fn is_zero(&self, p: &Poly) -> bool { p.is_zero() }
    pub fn zero(&self) -> Poly { Polynomial::zero() }
    pub fn one(&self) -> Poly { Polynomial::constant(self.ctx.field.one(), &self.ctx) }

    /// `*acc += other`. Replaces `acc` in-place.
    pub fn add_assign(&self, acc: &mut Poly, other: Poly) {
        let new = std::mem::replace(acc, Polynomial::zero()).add(&other, &self.ctx);
        *acc = new;
    }

    /// `*acc -= other`.
    pub fn sub_assign(&self, acc: &mut Poly, other: Poly) {
        let new = std::mem::replace(acc, Polynomial::zero()).sub(&other, &self.ctx);
        *acc = new;
    }
}

/// Iterator type returned by `PolyRingFacade::terms`. Each item is a
/// `(coefficient_ref, monomial)` pair.
pub struct TermsIter<'a> {
    poly: &'a Poly,
    ctx: &'a Arc<FfPolyRingCtx>,
    idx: usize,
}

impl<'a> Iterator for TermsIter<'a> {
    type Item = (&'a FfEl, Monomial);
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.poly.num_terms() { return None; }
        let t = self.poly.term(self.idx, self.ctx);
        let m = t.monomial();
        let c = t.coefficient();
        self.idx += 1;
        Some((c, m))
    }
}

/// Wrapper over the list of variables appearing in a polynomial. Supports
/// both `.is_empty()` and iteration over `usize` variable indices.
pub struct AppearingVars {
    vars: Vec<(usize, u16)>,
}

impl AppearingVars {
    pub fn is_empty(&self) -> bool { self.vars.is_empty() }
    pub fn len(&self) -> usize { self.vars.len() }
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.vars.iter().map(|(v, _)| *v)
    }
    pub fn into_iter(self) -> impl Iterator<Item = usize> {
        self.vars.into_iter().map(|(v, _)| v)
    }
    /// Access the underlying `(var_index, max_degree)` pair at position `i`.
    /// Provided for legacy `appearing[0]` indexing.
    pub fn get(&self, i: usize) -> (usize, usize) {
        let (v, d) = self.vars[i];
        (v, d as usize)
    }
}

impl std::ops::Index<usize> for AppearingVars {
    type Output = (usize, u16);
    fn index(&self, i: usize) -> &(usize, u16) { &self.vars[i] }
}

impl<'a> IntoIterator for &'a AppearingVars {
    type Item = &'a (usize, u16);
    type IntoIter = std::slice::Iter<'a, (usize, u16)>;
    fn into_iter(self) -> Self::IntoIter { self.vars.iter() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn test_poly_basic() {
        let field = FfField::new(BigUint::from(17u32));
        let pr = FfPolyRing::new(field, vec!["x".into(), "y".into()]);

        let x = pr.var(0);
        let y = pr.var(1);
        let sum = pr.add(x, y);
        assert!(!pr.is_zero(&sum));

        let neg_sum = pr.neg(pr.clone_poly(&sum));
        let zero = pr.add(sum, neg_sum);
        assert!(pr.is_zero(&zero));
    }
}
