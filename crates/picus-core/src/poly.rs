//! Multivariate polynomial ring over GF(p), backed by [`crate::ff`].
//!
//! Public surface: `FfPolyRing`, `Poly`, `Mono`, `pr.var(i)`,
//! `pr.constant(el)`, `pr.add/sub/mul/...`, and the inner `pr.ring.terms(&p)`
//! / `pr.ring.create_term(c, m)` / `pr.ring.exponent_at(m, i)` /
//! `pr.ring.appearing_indeterminates(&p)` / `pr.ring.indeterminate(i)`.
//! Storage and arithmetic are delegated to the [`crate::ff`] types.

use std::sync::Arc;

use crate::config::ReprKind;
use crate::ff::field::{FieldElem, PrimeField};
use crate::ff::monomial::{Monomial, MonomialOrder};
use crate::ff::polynomial::{DensePoly, PolyRing as FfPolyRingCtx, Polynomial};
use crate::ff::repr::MonomialRepr;
use crate::ff::sparse_polynomial::SparsePolynomial;

/// Re-export the polynomial type for the rest of the crate.
pub type Poly = Polynomial;
/// Re-export the monomial type.
pub type Mono = Monomial;
/// Type alias for the polynomial-ring facade. `&PolyRingType` is the
/// reference shape used throughout picus-solver.
pub type PolyRingType = PolyRingFacade;

/// A multivariate polynomial ring GF(p)[x_0, ..., x_{n-1}].
///
/// `pr.ring` is a thin facade around the underlying [`crate::ff::polynomial::PolyRing`]
/// context, exposing `terms`, `create_term`, `exponent_at`, etc.
pub struct FfPolyRing {
    pub ring: PolyRingFacade,
}

impl FfPolyRing {
    /// Create a new polynomial ring with degrevlex term order.
    pub fn new(field: PrimeField, var_names: Vec<String>) -> Self {
        let ctx = FfPolyRingCtx::new(field, var_names, MonomialOrder::DegRevLex);
        FfPolyRing { ring: PolyRingFacade { ctx } }
    }

    /// Like [`Self::new`] but with an explicit polynomial representation,
    /// bypassing the thread-local `config::poly_repr`.
    pub fn new_with_repr(field: PrimeField, var_names: Vec<String>, repr: ReprKind) -> Self {
        let ctx = FfPolyRingCtx::new_with_repr(field, var_names, MonomialOrder::DegRevLex, repr);
        FfPolyRing { ring: PolyRingFacade { ctx } }
    }

    /// Like [`Self::new`] but with an explicit term order (the
    /// representation still follows the thread-local `config::poly_repr`).
    /// Used to build a ring under a non-default order — e.g. an
    /// elimination order — so the whole order-agnostic GB pipeline reads a
    /// consistent order from the ring.
    pub fn new_with_order(field: PrimeField, var_names: Vec<String>, order: MonomialOrder) -> Self {
        let ctx = FfPolyRingCtx::new(field, var_names, order);
        FfPolyRing { ring: PolyRingFacade { ctx } }
    }

    /// The prime field, read from the shared ring context.
    pub fn field(&self) -> &PrimeField { &self.ring.ctx.field }
    /// Number of indeterminates.
    pub fn n_vars(&self) -> usize { self.ring.ctx.n_vars }
    /// Variable names, in index order.
    pub fn var_names(&self) -> &[String] { &self.ring.ctx.var_names }

    /// i-th indeterminate as a polynomial.
    pub fn var(&self, index: usize) -> Poly {
        Polynomial::variable(index, &self.ring.ctx)
    }

    /// Constant polynomial from a field element.
    pub fn constant(&self, el: FieldElem) -> Poly {
        Polynomial::constant(el, &self.ring.ctx)
    }

    pub fn zero(&self) -> Poly { Polynomial::zero() }
    pub fn one(&self) -> Poly { Polynomial::constant(self.ring.ctx.field.one(), &self.ring.ctx) }

    pub fn add(&self, a: Poly, b: Poly) -> Poly { a.add(&b, &self.ring.ctx) }
    pub fn sub(&self, a: Poly, b: Poly) -> Poly { a.sub(&b, &self.ring.ctx) }
    pub fn mul(&self, a: Poly, b: Poly) -> Poly { a.mul(&b, &self.ring.ctx) }
    pub fn neg(&self, a: Poly) -> Poly { a.negate(&self.ring.ctx) }
    pub fn clone_poly(&self, p: &Poly) -> Poly { p.clone() }
    pub fn is_zero(&self, p: &Poly) -> bool { p.is_zero() }

    /// Multiply polynomial by a scalar.
    pub fn scale(&self, coeff: FieldElem, poly: Poly) -> Poly {
        poly.scale(&coeff, &self.ring.ctx)
    }

    /// Look up variable index by name.
    pub fn var_index(&self, name: &str) -> Option<usize> {
        self.ring.ctx.var_names.iter().position(|n| n == name)
    }

    /// Reference to the underlying `ff::PolyRing` context.
    pub fn ctx(&self) -> &Arc<FfPolyRingCtx> { &self.ring.ctx }

    /// Variables that actually appear in `p` (delegates to the inner
    /// [`PolyRingFacade`]). Exposed here so the IR ring — which is just an
    /// `FfPolyRing` — offers the structural query the propagation lemmas use.
    pub fn appearing_indeterminates(&self, p: &Poly) -> AppearingVars {
        self.ring.appearing_indeterminates(p)
    }
}

/// Facade exposing the `.ring.` method surface used throughout
/// picus-solver. Holds a shared `Arc<ff::PolyRing>` context and
/// dispatches to the appropriate `Polynomial` / `Monomial` methods.
pub struct PolyRingFacade {
    pub ctx: Arc<FfPolyRingCtx>,
}

impl PolyRingFacade {
    pub fn n_vars(&self) -> usize { self.ctx.n_vars }

    pub fn var_names(&self) -> &[String] { &self.ctx.var_names }

    pub fn field(&self) -> &crate::ff::field::PrimeField { &self.ctx.field }

    /// Build a polynomial holding a single term `coeff * monomial`.
    pub fn create_term(&self, coeff: FieldElem, mono: Monomial) -> Poly {
        Polynomial::from_terms(vec![(mono, coeff)], &self.ctx)
    }

    /// Build a polynomial from an iterator of `(coeff, monomial)` pairs.
    /// The resulting polynomial is canonicalised (terms summed/sorted).
    pub fn from_terms<I>(&self, terms: I) -> Poly
    where I: IntoIterator<Item = (FieldElem, Monomial)>,
    {
        let v: Vec<(Monomial, FieldElem)> = terms.into_iter().map(|(c, m)| (m, c)).collect();
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
        match p {
            Polynomial::Dense(d) => TermsIter::Dense { poly: d, ctx: &self.ctx, idx: 0 },
            Polynomial::Sparse(s) => TermsIter::Sparse { poly: s, idx: 0 },
        }
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

/// Iterator type returned by `PolyRingFacade::terms`, yielding
/// `(coefficient_ref, monomial)` for either representation. The sparse
/// arm materialises one dense `Monomial` per term (transient); hot
/// readers should prefer `Polynomial::collect_terms_idx`, which stays
/// sparse.
pub enum TermsIter<'a> {
    Dense { poly: &'a DensePoly, ctx: &'a Arc<FfPolyRingCtx>, idx: usize },
    Sparse { poly: &'a SparsePolynomial, idx: usize },
}

impl<'a> Iterator for TermsIter<'a> {
    type Item = (&'a FieldElem, Monomial);
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TermsIter::Dense { poly, ctx, idx } => {
                if *idx >= poly.num_terms() {
                    return None;
                }
                let t = poly.term(*idx, ctx);
                let m = t.monomial();
                let c = t.coefficient();
                *idx += 1;
                Some((c, m))
            }
            TermsIter::Sparse { poly, idx } => {
                let (m, c) = poly.term_at(*idx)?;
                *idx += 1;
                Some((c, Monomial::from_exponents(MonomialRepr::to_dense(m))))
            }
        }
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
    /// Access the underlying `(var_index, max_degree)` pair at
    /// position `i`. Used by callers that index `appearing[0]`
    /// directly (e.g. univariate-detection paths).
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

// ─── IR-layer polynomial ────────────────────────────────────────────
//
// The IR layer and the engine share one dense/sparse polynomial type, so
// the IR ring is just [`FfPolyRing`] (its method surface already covers
// everything `picus-smt`'s `PolyIR` needs) and the IR polynomial is
// `IrPoly`, an alias for [`Polynomial`]. Keeping the alias documents intent
// at the `picus-smt` / `picus-analysis` use sites without a second facade.

/// IR polynomial — the dense/sparse `Polynomial` enum.
pub type IrPoly = Polynomial;

#[cfg(test)]
#[path = "poly_tests.rs"]
mod tests;
