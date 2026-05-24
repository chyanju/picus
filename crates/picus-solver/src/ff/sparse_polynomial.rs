//! Sparse multivariate polynomial: a list of `(SparseMonomial, coeff)`
//! terms, sorted descending by the ring's monomial order, coeffs nonzero.
//!
//! Pairs with [`SparseMonomial`] so the polynomial layer scales to many
//! variables. This is the L1 surface — construction, `add`/`sub`/`mul`,
//! `evaluate`, leading-term, term iteration — that the IR, lowering, and
//! the cvc5 lowering path need. Gröbner reduction over the sparse
//! representation is a later stage. Validated against the dense
//! `Polynomial` by `repr_oracle`.

use std::cmp::Ordering;

use super::field::FieldElem;
use super::polynomial::PolyRing;
use super::repr::MonomialRepr;
use super::sparse_monomial::SparseMonomial;

#[derive(Clone, Debug)]
pub struct SparsePolynomial {
    /// Sorted DESCENDING by the ring order; every coefficient nonzero.
    terms: Vec<(SparseMonomial, FieldElem)>,
}

impl SparsePolynomial {
    pub fn zero() -> Self {
        SparsePolynomial { terms: Vec::new() }
    }

    pub fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        if ring.field.is_zero(&c) {
            return Self::zero();
        }
        SparsePolynomial { terms: vec![(SparseMonomial::one(ring.n_vars), c)] }
    }

    pub fn variable(var: usize, ring: &PolyRing) -> Self {
        SparsePolynomial {
            terms: vec![(SparseMonomial::single_var(ring.n_vars, var, 1), ring.field.one())],
        }
    }

    /// Build from arbitrary `(monomial, coeff)` pairs: drop zero coeffs,
    /// sort descending by the ring order, combine like monomials.
    pub fn from_terms(mut terms: Vec<(SparseMonomial, FieldElem)>, ring: &PolyRing) -> Self {
        terms.retain(|(_, c)| !ring.field.is_zero(c));
        terms.sort_by(|a, b| b.0.cmp_with_order(&a.0, ring.order));
        let mut out: Vec<(SparseMonomial, FieldElem)> = Vec::with_capacity(terms.len());
        for (m, c) in terms {
            if let Some(last) = out.last_mut() {
                if last.0 == m {
                    let s = ring.field.add(&last.1, &c);
                    if ring.field.is_zero(&s) {
                        out.pop();
                    } else {
                        last.1 = s;
                    }
                    continue;
                }
            }
            out.push((m, c));
        }
        SparsePolynomial { terms: out }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }
    pub fn total_degree(&self) -> u32 {
        self.terms.first().map(|(m, _)| m.total_degree()).unwrap_or(0)
    }
    pub fn is_constant(&self) -> bool {
        match self.terms.len() {
            0 => true,
            1 => self.terms[0].0.is_one(),
            _ => false,
        }
    }
    pub fn leading_term(&self) -> Option<&(SparseMonomial, FieldElem)> {
        self.terms.first()
    }
    pub fn leading_monomial(&self) -> Option<&SparseMonomial> {
        self.terms.first().map(|(m, _)| m)
    }
    pub fn leading_coefficient(&self) -> Option<&FieldElem> {
        self.terms.first().map(|(_, c)| c)
    }
    pub fn iter_terms(&self) -> impl Iterator<Item = (&SparseMonomial, &FieldElem)> {
        self.terms.iter().map(|(m, c)| (m, c))
    }

    pub fn negate(&self, ring: &PolyRing) -> Self {
        SparsePolynomial {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), ring.field.neg(c))).collect(),
        }
    }

    pub fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Self {
        if ring.field.is_zero(c) {
            return Self::zero();
        }
        if ring.field.is_one(c) {
            return self.clone();
        }
        SparsePolynomial {
            terms: self.terms.iter().map(|(m, x)| (m.clone(), ring.field.mul(x, c))).collect(),
        }
    }

    pub fn add(&self, other: &Self, ring: &PolyRing) -> Self {
        self.merge(other, ring, false)
    }
    pub fn sub(&self, other: &Self, ring: &PolyRing) -> Self {
        self.merge(other, ring, true)
    }

    fn merge(&self, other: &Self, ring: &PolyRing, neg_other: bool) -> Self {
        let mut out = Vec::with_capacity(self.terms.len() + other.terms.len());
        let (mut i, mut j) = (0usize, 0usize);
        let other_coeff = |j: usize| {
            if neg_other {
                ring.field.neg(&other.terms[j].1)
            } else {
                other.terms[j].1.clone()
            }
        };
        while i < self.terms.len() && j < other.terms.len() {
            match self.terms[i].0.cmp_with_order(&other.terms[j].0, ring.order) {
                Ordering::Greater => {
                    out.push(self.terms[i].clone());
                    i += 1;
                }
                Ordering::Less => {
                    out.push((other.terms[j].0.clone(), other_coeff(j)));
                    j += 1;
                }
                Ordering::Equal => {
                    let s = if neg_other {
                        ring.field.sub(&self.terms[i].1, &other.terms[j].1)
                    } else {
                        ring.field.add(&self.terms[i].1, &other.terms[j].1)
                    };
                    if !ring.field.is_zero(&s) {
                        out.push((self.terms[i].0.clone(), s));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        while i < self.terms.len() {
            out.push(self.terms[i].clone());
            i += 1;
        }
        while j < other.terms.len() {
            out.push((other.terms[j].0.clone(), other_coeff(j)));
            j += 1;
        }
        SparsePolynomial { terms: out }
    }

    pub fn mul(&self, other: &Self, ring: &PolyRing) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut acc = Vec::with_capacity(self.terms.len() * other.terms.len());
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                acc.push((MonomialRepr::mul(ma, mb), ring.field.mul(ca, cb)));
            }
        }
        Self::from_terms(acc, ring)
    }

    pub fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem {
        let mut acc = ring.field.zero();
        for (m, c) in &self.terms {
            let mut term = c.clone();
            m.for_each_nonzero(|v, e| {
                let p = ring.field.pow_u64(&values[v], e as u64);
                ring.field.mul_assign(&mut term, &p);
            });
            ring.field.add_assign(&mut acc, &term);
        }
        acc
    }
}

impl super::repr::PolyRepr for SparsePolynomial {
    type Mono = SparseMonomial;

    fn zero() -> Self {
        SparsePolynomial::zero()
    }
    fn constant(c: FieldElem, ring: &PolyRing) -> Self {
        SparsePolynomial::constant(c, ring)
    }
    fn variable(var: usize, ring: &PolyRing) -> Self {
        SparsePolynomial::variable(var, ring)
    }
    fn from_terms(terms: Vec<(SparseMonomial, FieldElem)>, ring: &PolyRing) -> Self {
        SparsePolynomial::from_terms(terms, ring)
    }
    fn is_zero(&self) -> bool {
        SparsePolynomial::is_zero(self)
    }
    fn num_terms(&self) -> usize {
        SparsePolynomial::num_terms(self)
    }
    fn add(&self, other: &Self, ring: &PolyRing) -> Self {
        SparsePolynomial::add(self, other, ring)
    }
    fn sub(&self, other: &Self, ring: &PolyRing) -> Self {
        SparsePolynomial::sub(self, other, ring)
    }
    fn mul(&self, other: &Self, ring: &PolyRing) -> Self {
        SparsePolynomial::mul(self, other, ring)
    }
    fn scale(&self, c: &FieldElem, ring: &PolyRing) -> Self {
        SparsePolynomial::scale(self, c, ring)
    }
    fn negate(&self, ring: &PolyRing) -> Self {
        SparsePolynomial::negate(self, ring)
    }
    fn evaluate(&self, values: &[FieldElem], ring: &PolyRing) -> FieldElem {
        SparsePolynomial::evaluate(self, values, ring)
    }
    fn collect_terms_idx(&self, ring: &PolyRing) -> Vec<(num_bigint::BigUint, Vec<(usize, u16)>)> {
        self.iter_terms()
            .map(|(m, c)| {
                let coeff = ring.field.to_biguint(c);
                let mut vars = Vec::new();
                m.for_each_nonzero(|v, e| vars.push((v, e)));
                (coeff, vars)
            })
            .collect()
    }
}
