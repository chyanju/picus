//! Geobucket (Yan 1998) for the sparse polynomial representation, and the
//! geobucket-backed multivariate reduction it powers.
//!
//! Mirror of [`super::geobucket`] over `(SparseMonomial, FieldElem)` term
//! lists kept sorted descending by the ring order. A geobucket is a set of
//! buckets of geometrically increasing capacity; adding a length-`L`
//! polynomial costs amortised O(L·log(N/L)) instead of the O(N) a single
//! re-sorted accumulator pays per step. That is the dominant cost of
//! multi-step reduction, where the naive accumulator additionally pays
//! O(N) to drop each leading term.
//!
//! Key sparse simplification over the dense geobucket: multiplying a
//! sorted-descending polynomial by a single monomial preserves the order
//! (the monomial order is multiplicative), so the scaled divisor tail in
//! [`SparseGeobucket::sub_scaled_tail`] needs no re-sort.

use std::cmp::Ordering;

use super::divmask::DivMask;
use super::field::FieldElem;
use super::polynomial::PolyRing;
use super::repr::MonomialRepr;
use super::sparse_monomial::SparseMonomial;
use super::sparse_polynomial::SparsePolynomial;

type Term = (SparseMonomial, FieldElem);

/// Smallest bucket capacity (in terms).
const BASE_CAPACITY: usize = 128;
/// Geometric growth factor between consecutive buckets.
const RATIO: usize = 4;
/// Hard cap on the number of buckets (128·4^19 ≈ 10^13 terms).
const MAX_BUCKETS: usize = 20;

/// A geobucket: `buckets[i]` is a descending-sorted term list with a
/// `heads[i]` cursor, so popping a leading term advances the cursor in O(1)
/// instead of shifting the vector.
struct SparseGeobucket<'r> {
    buckets: Vec<Vec<Term>>,
    heads: Vec<usize>,
    ring: &'r PolyRing,
}

impl<'r> SparseGeobucket<'r> {
    fn new(ring: &'r PolyRing) -> Self {
        SparseGeobucket { buckets: Vec::new(), heads: Vec::new(), ring }
    }

    /// Capacity of bucket `idx`: `BASE_CAPACITY · RATIO^idx`, saturating.
    fn capacity(idx: usize) -> usize {
        let mut cap = BASE_CAPACITY;
        for _ in 0..idx {
            cap = match cap.checked_mul(RATIO) {
                Some(v) => v,
                None => return usize::MAX,
            };
        }
        cap
    }

    /// Smallest bucket index whose capacity is `>= len`, capped.
    fn fitting_bucket(len: usize) -> usize {
        let mut idx = 0usize;
        let mut cap = BASE_CAPACITY;
        while cap < len && idx + 1 < MAX_BUCKETS {
            idx += 1;
            cap = cap.saturating_mul(RATIO);
        }
        idx
    }

    fn ensure_bucket(&mut self, idx: usize) {
        while self.buckets.len() <= idx {
            self.buckets.push(Vec::new());
            self.heads.push(0);
        }
    }

    fn bucket_is_empty(&self, idx: usize) -> bool {
        idx >= self.buckets.len() || self.heads[idx] >= self.buckets[idx].len()
    }

    /// Move the live tail (`terms[head..]`) of bucket `idx` out, leaving
    /// the bucket empty. No coefficient cloning — the tail is moved.
    fn take_bucket_live(&mut self, idx: usize) -> Vec<Term> {
        if idx >= self.buckets.len() {
            return Vec::new();
        }
        let head = self.heads[idx];
        self.heads[idx] = 0;
        let mut existing = std::mem::take(&mut self.buckets[idx]);
        if head == 0 {
            return existing;
        }
        if head >= existing.len() {
            return Vec::new();
        }
        existing.split_off(head)
    }

    /// Merge two descending-sorted term lists, summing equal monomials and
    /// dropping zero sums. O(|a| + |b|).
    fn merge_terms(ring: &PolyRing, a: Vec<Term>, b: Vec<Term>) -> Vec<Term> {
        let order = ring.order;
        let mut out: Vec<Term> = Vec::with_capacity(a.len() + b.len());
        let mut ai = a.into_iter().peekable();
        let mut bi = b.into_iter().peekable();
        loop {
            match (ai.peek(), bi.peek()) {
                (Some((ma, _)), Some((mb, _))) => match ma.cmp_with_order(mb, order) {
                    Ordering::Greater => out.push(ai.next().unwrap()),
                    Ordering::Less => out.push(bi.next().unwrap()),
                    Ordering::Equal => {
                        let (m, ca) = ai.next().unwrap();
                        let (_, cb) = bi.next().unwrap();
                        let s = ring.field.add(&ca, &cb);
                        if !ring.field.is_zero(&s) {
                            out.push((m, s));
                        }
                    }
                },
                (Some(_), None) => {
                    out.extend(ai);
                    break;
                }
                (None, Some(_)) => {
                    out.extend(bi);
                    break;
                }
                (None, None) => break,
            }
        }
        out
    }

    /// Add a descending-sorted, nonzero-coefficient term list, cascading
    /// merges up through the buckets on overflow.
    fn add_terms(&mut self, p: Vec<Term>) {
        if p.is_empty() {
            return;
        }
        let mut cur = p;
        let mut idx = Self::fitting_bucket(cur.len());
        loop {
            self.ensure_bucket(idx);
            if self.bucket_is_empty(idx) {
                let cap = Self::capacity(idx);
                if cur.len() <= cap || idx + 1 >= MAX_BUCKETS {
                    self.buckets[idx] = cur;
                    self.heads[idx] = 0;
                    return;
                }
                idx += 1;
                continue;
            }
            let live = self.take_bucket_live(idx);
            let merged = Self::merge_terms(self.ring, live, cur);
            if merged.is_empty() {
                return;
            }
            let cap = Self::capacity(idx);
            if merged.len() <= cap || idx + 1 >= MAX_BUCKETS {
                self.buckets[idx] = merged;
                self.heads[idx] = 0;
                return;
            }
            cur = merged;
            idx += 1;
        }
    }

    /// Pop the leading term across all buckets, summing coefficients of
    /// buckets that share the leading monomial and skipping a cancelled
    /// (zero) sum. O(num_buckets) per call.
    fn pop_leading_term(&mut self) -> Option<Term> {
        let order = self.ring.order;
        loop {
            let mut best: Option<usize> = None;
            for i in 0..self.buckets.len() {
                if self.bucket_is_empty(i) {
                    continue;
                }
                match best {
                    None => best = Some(i),
                    Some(b) => {
                        let mi = &self.buckets[i][self.heads[i]].0;
                        let mb = &self.buckets[b][self.heads[b]].0;
                        if mi.cmp_with_order(mb, order) == Ordering::Greater {
                            best = Some(i);
                        }
                    }
                }
            }
            let best = best?;
            let (lead, mut coeff) = {
                let (m, c) = &self.buckets[best][self.heads[best]];
                (m.clone(), c.clone())
            };
            self.heads[best] += 1;
            for i in 0..self.buckets.len() {
                if i == best || self.bucket_is_empty(i) {
                    continue;
                }
                if self.buckets[i][self.heads[i]].0 == lead {
                    self.ring
                        .field
                        .add_assign(&mut coeff, &self.buckets[i][self.heads[i]].1);
                    self.heads[i] += 1;
                }
            }
            if !self.ring.field.is_zero(&coeff) {
                return Some((lead, coeff));
            }
            // Cancelled: keep scanning for the next leading term.
        }
    }

    /// Add `neg_coeff · shift · (divisor without its leading term)` to the
    /// geobucket. Used in reduction where the divisor's leading term
    /// exactly cancels the already-popped leading term. The scaled tail is
    /// still descending (multiplication preserves the order) with nonzero
    /// coefficients (field, no zero divisors), so it is a valid bucket.
    fn sub_scaled_tail(&mut self, shift: &SparseMonomial, neg_coeff: &FieldElem, divisor: &[Term]) {
        if divisor.len() <= 1 || self.ring.field.is_zero(neg_coeff) {
            return;
        }
        let mut scaled: Vec<Term> = Vec::with_capacity(divisor.len() - 1);
        for (m, c) in &divisor[1..] {
            let nm = MonomialRepr::mul(shift, m);
            let nc = self.ring.field.mul(c, neg_coeff);
            scaled.push((nm, nc));
        }
        self.add_terms(scaled);
    }
}

/// Normal form of `subject` modulo `divisors` via the sparse geobucket.
/// Pops leading terms in descending order; each is either cancelled by the
/// first divisor whose leading monomial divides it (subtract the scaled
/// divisor tail) or, if irreducible, appended to the result. The result
/// stream is descending and duplicate-free, so it is canonical.
pub(super) fn reduce(
    subject: &SparsePolynomial,
    divisors: &[&SparsePolynomial],
    ring: &PolyRing,
) -> SparsePolynomial {
    // Cache each divisor's leading (monomial, coeff) and a presence
    // DivMask of its leading monomial for O(1) divisibility rejection.
    let div_lt: Vec<Option<(&SparseMonomial, &FieldElem)>> =
        divisors.iter().map(|d| d.leading_term().map(|(m, c)| (m, c))).collect();
    let div_mask: Vec<DivMask> = div_lt
        .iter()
        .map(|lt| lt.map_or(DivMask::empty(), |(m, _)| m.divmask()))
        .collect();

    let mut gb = SparseGeobucket::new(ring);
    gb.add_terms(subject.terms_ref().to_vec());

    let mut result: Vec<Term> = Vec::new();
    while let Some((lm, lc)) = gb.pop_leading_term() {
        let lm_mask = lm.divmask();
        let mut chosen: Option<usize> = None;
        for (di, lt) in div_lt.iter().enumerate() {
            if let Some((dlm, _)) = *lt {
                // DivMask prefilter: a divisor LT with a variable absent
                // from `lm` cannot divide it.
                if !div_mask[di].divides_consistent_with(lm_mask) {
                    continue;
                }
                if MonomialRepr::divides(dlm, &lm) {
                    chosen = Some(di);
                    break;
                }
            }
        }
        match chosen {
            Some(di) => {
                let (dlm, dlc) = div_lt[di].unwrap();
                let ratio = ring.field.div(&lc, dlc).expect("divisor leading coeff is nonzero");
                let neg_ratio = ring.field.neg(&ratio);
                let shift = MonomialRepr::div(&lm, dlm);
                gb.sub_scaled_tail(&shift, &neg_ratio, divisors[di].terms_ref());
            }
            None => {
                // Irreducible leading term: popped in descending order, so
                // pushing keeps `result` descending.
                result.push((lm, lc));
            }
        }
    }
    SparsePolynomial::from_sorted_terms(result)
}
