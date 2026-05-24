//! Sparse multivariate polynomial: a list of `(SparseMonomial, coeff)`
//! terms, sorted descending by the ring's monomial order, coeffs nonzero.
//!
//! Stores only nonzero entries, so it scales to rings with many variables
//! where the dense [`DensePoly`] would carry a full-length exponent vector
//! per term. Provides construction, ring arithmetic, evaluation, term
//! iteration, and multivariate reduction (Gröbner-basis computation builds
//! on these in `sparse_gb`). Validated against `DensePoly` by `repr_oracle`.

use std::cmp::Ordering;

use super::field::FieldElem;
use super::monomial::Monomial;
use super::polynomial::{PolyRing, DensePoly};
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

    /// Variables that appear (nonzero exponent) in any term, ascending by
    /// index, paired with their max exponent. Sparse-native (O(nnz)); no
    /// dense materialisation.
    pub fn appearing_variables(&self) -> Vec<(usize, u16)> {
        let mut max_deg: std::collections::BTreeMap<usize, u16> = std::collections::BTreeMap::new();
        for (m, _) in &self.terms {
            m.for_each_nonzero(|v, e| {
                let slot = max_deg.entry(v).or_insert(0);
                if e > *slot {
                    *slot = e;
                }
            });
        }
        max_deg.into_iter().collect()
    }

    /// Content fingerprint for incremental-GB caching (matches the role
    /// of `DensePoly::content_hash`; need not agree across arms since a
    /// run uses a single representation).
    pub fn content_hash(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.terms.len().hash(&mut h);
        for (m, c) in &self.terms {
            m.hash(&mut h);
            c.hash(&mut h);
        }
        h.finish()
    }

    /// The `idx`-th `(monomial, coeff)` term in descending ring order,
    /// or `None` past the end. Lets a positional iterator walk the terms
    /// without exposing the backing vector.
    pub fn term_at(&self, idx: usize) -> Option<(&SparseMonomial, &FieldElem)> {
        self.terms.get(idx).map(|(m, c)| (m, c))
    }

    /// The backing term list (descending ring order, nonzero coeffs).
    /// For the sparse geobucket: seed the subject and read divisor tails.
    pub(crate) fn terms_ref(&self) -> &[(SparseMonomial, FieldElem)] {
        &self.terms
    }

    /// Build directly from a term list that is already in canonical form
    /// (sorted descending by the ring order, every coeff nonzero, no
    /// duplicate monomials) — e.g. the descending stream of irreducible
    /// terms the geobucket reducer collects. Skips the `from_terms`
    /// sort/combine pass.
    pub(crate) fn from_sorted_terms(terms: Vec<(SparseMonomial, FieldElem)>) -> Self {
        SparsePolynomial { terms }
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

    /// Normal form of `self` modulo `divisors` (multivariate division),
    /// the production entry point: routed through the sparse geobucket
    /// ([`super::sparse_geobucket`]) so multi-step reduction is amortised
    /// instead of paying an O(n) leading-term removal and full re-merge per
    /// step. Same divisor-selection rule (first divisor by index whose
    /// leading monomial divides the current one) as
    /// [`Self::reduce_by_refs_naive`], so the two agree term-for-term
    /// (`repr_oracle` checks that).
    pub fn reduce_by_refs(&self, divisors: &[&SparsePolynomial], ring: &PolyRing) -> SparsePolynomial {
        if self.is_zero() || divisors.is_empty() {
            return self.clone();
        }
        super::sparse_geobucket::reduce(self, divisors, ring)
    }

    /// Reference multivariate division: keep the partially-reduced
    /// polynomial in one descending-sorted vector, cancelling the leading
    /// term against the first divisor that divides it. O(n) per step; the
    /// geobucket [`Self::reduce_by_refs`] is the production path. The dense
    /// `DensePoly::reduce_by_refs_naive` is the differential oracle for this
    /// (same divisor order ⇒ identical normal form).
    pub fn reduce_by_refs_naive(&self, divisors: &[&SparsePolynomial], ring: &PolyRing) -> SparsePolynomial {
        if self.is_zero() {
            return self.clone();
        }
        // Leading (monomial, coeff) of each divisor that has one.
        let div_lt: Vec<Option<(SparseMonomial, FieldElem)>> =
            divisors.iter().map(|d| d.terms.first().cloned()).collect();

        let mut current = self.clone();
        let mut result: Vec<(SparseMonomial, FieldElem)> = Vec::new();

        while let Some((lm, lc)) = current.terms.first().cloned() {
            let mut chosen: Option<usize> = None;
            for (di, lt) in div_lt.iter().enumerate() {
                if let Some((dlm, _)) = lt {
                    if MonomialRepr::divides(dlm, &lm) {
                        chosen = Some(di);
                        break;
                    }
                }
            }
            match chosen {
                Some(di) => {
                    let (dlm, dlc) = div_lt[di].as_ref().unwrap();
                    let ratio = ring
                        .field
                        .div(&lc, dlc)
                        .expect("divisor leading coefficient is nonzero");
                    let neg_ratio = ring.field.neg(&ratio);
                    let shift = MonomialRepr::div(&lm, dlm);
                    // current += (-ratio · shift) · divisor  ⇒ cancels the leading term.
                    let factor = SparsePolynomial::from_terms(vec![(shift, neg_ratio)], ring);
                    let prod = factor.mul(divisors[di], ring);
                    current = current.add(&prod, ring);
                }
                None => {
                    // Irreducible leading term: move it to the result and
                    // drop it from `current` (terms stay sorted descending).
                    result.push((lm, lc));
                    current.terms.remove(0);
                }
            }
        }
        SparsePolynomial::from_terms(result, ring)
    }

    /// Scale so the leading coefficient is 1; the zero polynomial stays zero.
    pub fn make_monic(&self, ring: &PolyRing) -> SparsePolynomial {
        match self.terms.first() {
            None => SparsePolynomial::zero(),
            Some((_, lc)) => {
                if ring.field.is_one(lc) {
                    self.clone()
                } else {
                    let lc_inv = ring.field.inv(lc).expect("nonzero leading coefficient");
                    self.scale(&lc_inv, ring)
                }
            }
        }
    }

    /// Build a sparse polynomial from a dense one (same terms). The
    /// boundary conversion the native GB dispatch uses when routing a
    /// dense-built generator set through the sparse engine.
    pub fn from_dense(p: &DensePoly, ring: &PolyRing) -> Self {
        let mut terms: Vec<(SparseMonomial, FieldElem)> = Vec::with_capacity(p.num_terms());
        for i in 0..p.num_terms() {
            let t = p.term(i, ring);
            terms.push((SparseMonomial::from_exponents(t.exponents().to_vec()), t.coefficient().clone()));
        }
        // Dense terms are already sorted/canonical; from_terms re-canonicalises
        // (cheap) and guarantees the sparse invariants regardless.
        SparsePolynomial::from_terms(terms, ring)
    }

    /// Materialise a dense polynomial with the same terms.
    pub fn to_dense(&self, ring: &PolyRing) -> DensePoly {
        let terms: Vec<(Monomial, FieldElem)> = self
            .terms
            .iter()
            .map(|(m, c)| (Monomial::from_exponents(MonomialRepr::to_dense(m)), c.clone()))
            .collect();
        DensePoly::from_terms(terms, ring)
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
