//! Ideal operations over GF(p)[x_1, ..., x_n].
//!
//! Thin shim over the in-tree [`crate::ff`] Buchberger / Ideal
//! implementation. Public API: [`Ideal`], [`compute_gb_with_order`],
//! [`compute_gb_with_order_traced`], [`interreduce_basis`],
//! [`leading_monomial`], [`leading_coefficient`],
//! [`GbAlgorithm`], [`last_dispatched_algorithm`].

use std::collections::HashSet;

use crate::ff::buchberger::{self, poly_coefficient_at};
use crate::ff::polynomial::Polynomial;
use crate::ff::monomial::Monomial;
use crate::ff::monomial::MonomialOrder as FfOrder;
use crate::ff::field::FieldElem;
use crate::metric;
use crate::poly::{FfPolyRing, Mono, Poly, PolyRingType};
use crate::timeout::{CancelToken, Cancelled};

mod engine;
pub use engine::*;

// ─────────────────────────────── Ideal ─────────────────────────────────────

/// A Groebner basis equipped with the data needed for ideal operations.
pub struct Ideal<'r> {
    pub poly_ring: &'r FfPolyRing,
    /// A Groebner basis (in `DegRevLex` order) of the ideal.
    pub basis: Vec<Poly>,
}

impl<'r> Ideal<'r> {
    /// Wrap an existing list of polynomials as the GB of an ideal.
    pub fn from_gb(poly_ring: &'r FfPolyRing, basis: Vec<Poly>) -> Self {
        Ideal { poly_ring, basis }
    }

    /// Build an ideal by computing its DegRevLex Groebner basis.
    pub fn new(poly_ring: &'r FfPolyRing, generators: Vec<Poly>) -> Self {
        // Delegates to the cancel-aware variant with a never-firing
        // token so both entry points produce identical bases
        // (including the `interreduce_basis` pass after Buchberger's
        // internal finalisation). The `Err` arm is unreachable with
        // a never-firing token; the empty-ideal fallback keeps `new`
        // total.
        Self::new_with_cancel(poly_ring, generators, &CancelToken::none())
            .unwrap_or_else(|_| Ideal { poly_ring, basis: Vec::new() })
    }

    /// Build an ideal with cooperative cancellation.
    pub fn new_with_cancel(
        poly_ring: &'r FfPolyRing,
        generators: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        if generators.is_empty() {
            return Ok(Ideal { poly_ring, basis: Vec::new() });
        }
        // Route through compute_gb_with_order rather than compute_gb_dispatch
        // directly, so the split-GB path (this constructor's main caller)
        // honours the configured representation (sparse by default, via
        // use_sparse_gb) and the shared finish_gb cancel/error/backup
        // contract. A genuine engine error yields an empty basis (not the
        // unreduced generators): downstream that reads as "no constraints",
        // never a trusted GB, and the post-call is_cancelled checks turn a
        // cancellation into Err(Cancelled) as before.
        let basis = compute_gb_with_order(poly_ring, generators, cancel, FfOrder::DegRevLex);
        if cancel.is_cancelled() { return Err(Cancelled); }
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Extend an existing ideal by adding new generators incrementally.
    ///
    /// Reuses the existing reduced GB and runs incremental Buchberger
    /// seeded with the existing basis, computing only cross / intra
    /// S-pairs involving the new generators. The final GB equals the
    /// one obtained by full recomputation on the union of generators.
    pub(crate) fn extend_with_cancel(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        if crate::profile::gb_stats_enabled() {
            crate::profile::SPLIT_GB.extend_with_cancel_calls
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !f.is_zero())
            .collect();
        if new_polys.is_empty() {
            if crate::profile::gb_stats_enabled() {
                crate::profile::SPLIT_GB.extend_no_op_skips
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            return Ok(self);
        }
        // Pre-reduce new generators against the existing reduced GB.
        // If every new polynomial reduces to zero, the ideal is unchanged
        // and the entire incremental Buchberger + interreduce round-trip
        // can be skipped.
        let surviving: Vec<Poly> = if self.basis.is_empty() {
            new_polys
        } else {
            let basis_refs: Vec<&Poly> = self.basis.iter().collect();
            let ring = self.poly_ring.ctx();
            new_polys.into_iter()
                .map(|p| p.reduce_by_refs_cancel(&basis_refs, ring, cancel))
                .filter(|p| !p.is_zero())
                .collect()
        };
        if cancel.is_cancelled() { return Err(Cancelled); }
        if surviving.is_empty() {
            if crate::profile::gb_stats_enabled() {
                crate::profile::SPLIT_GB.extend_no_op_skips
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order(
            poly_ring, known_gb, surviving, cancel, FfOrder::DegRevLex,
        );
        if cancel.is_cancelled() { return Err(Cancelled); }
        let basis = interreduce_basis(poly_ring, basis, cancel);
        if cancel.is_cancelled() { return Err(Cancelled); }
        Ok(Ideal { poly_ring, basis })
    }

    /// Traced variant of `extend_with_cancel`.
    ///
    /// Feeds Buchberger observer events to the supplied `tracer`, which
    /// must be sized for at least `self.basis.len() + new_polys.len()` (after
    /// the zero filter). The caller drives UNSAT-core extraction from the
    /// populated tracer.
    ///
    /// The tracer's input numbering matches the order generators are added:
    /// first all elements of `self.basis` (already a reduced GB), then all
    /// surviving `new_polys`.
    pub(crate) fn extend_with_cancel_traced(
        self,
        new_polys: Vec<Poly>,
        cancel: &CancelToken,
        tracer: &mut crate::gb::tracer::GbTracer,
    ) -> Result<Self, Cancelled> {
        if cancel.is_cancelled() { return Err(Cancelled); }
        let new_polys: Vec<Poly> = new_polys.into_iter()
            .filter(|f| !f.is_zero())
            .collect();
        if new_polys.is_empty() {
            return Ok(self);
        }
        let Ideal { poly_ring, basis: known_gb } = self;
        let basis = compute_gb_incremental_with_order_traced(
            poly_ring, known_gb, new_polys, cancel, FfOrder::DegRevLex, tracer,
        );
        if cancel.is_cancelled() { return Err(Cancelled); }
        // NOTE: do NOT inter-reduce here — the trivial-element parents in
        // `tracer` are precise only when Buchberger aborted on trivial.
        // Inter-reduce would mutate basis indices and require additional
        // dep tracking; for the linear-fast-path UNSAT detection we only
        // need to know is_whole_ring, which is preserved.
        Ok(Ideal { poly_ring, basis })
    }

    /// Reduce `p` modulo the ideal. Returns the *normal form* of `p`.
    pub fn reduce(&self, p: &Poly) -> Poly {
        if self.basis.is_empty() {
            return p.clone();
        }
        let ring = &self.poly_ring.ctx();
        p.reduce_by(&self.basis, ring)
    }

    /// Cancel-aware reduce. On cancel returns whatever partial remainder
    /// the geobucket reducer had accumulated — sound (still represents the
    /// same residue class) but not a normal form, so callers that want
    /// `is_zero` membership semantics must check `cancel.is_cancelled()`
    /// themselves to distinguish "really not in I" from "ran out of time."
    pub fn reduce_with_cancel(&self, p: &Poly, cancel: &CancelToken) -> Poly {
        if self.basis.is_empty() {
            return p.clone();
        }
        let ring = self.poly_ring.ctx();
        let refs: Vec<&Poly> = self.basis.iter().collect();
        p.reduce_by_refs_cancel(&refs, ring, cancel)
    }

    /// Ideal membership: returns `true` iff `p ∈ I`.
    pub fn contains(&self, p: &Poly) -> bool {
        self.reduce(p).is_zero()
    }

    /// Cancel-aware membership test. On cancel returns the value computed
    /// from a partial reduction, which may falsely report "not in I" if
    /// cancellation interrupts mid-reduce. Callers should treat a `false`
    /// result with a cancelled token as "unknown, please retry / abort".
    pub fn contains_with_cancel(&self, p: &Poly, cancel: &CancelToken) -> bool {
        self.reduce_with_cancel(p, cancel).is_zero()
    }

    /// Returns `true` iff `I = R` (i.e. `1 ∈ I`).
    pub fn is_whole_ring(&self) -> bool {
        self.basis.iter().any(|p| !p.is_zero() && p.is_constant())
    }

    /// Returns `true` iff `R/I` is a finite-dimensional `K`-vector space.
    pub fn is_zero_dim(&self) -> bool {
        if self.is_whole_ring() {
            return true;
        }
        if self.basis.is_empty() {
            return false;
        }
        let ring = self.poly_ring.ctx();
        let n_vars = self.poly_ring.n_vars();

        let mut covered: HashSet<usize> = HashSet::new();
        for p in &self.basis {
            if p.is_zero() { continue; }
            if let Some(lm) = p.leading_monomial(ring) {
                let exps = lm.exponents();
                let mut nonzero_var: Option<usize> = None;
                let mut multiple = false;
                for i in 0..n_vars {
                    if exps[i] > 0 {
                        if nonzero_var.is_some() {
                            multiple = true;
                            break;
                        }
                        nonzero_var = Some(i);
                    }
                }
                if !multiple {
                    if let Some(i) = nonzero_var {
                        covered.insert(i);
                    }
                }
            }
        }
        covered.len() == n_vars
    }

    /// `dim_k(R/I)` — the number of standard monomials, equivalently the
    /// number of solutions of `I` with multiplicity over the algebraic
    /// closure — read off the leading monomials of this basis via the
    /// Hilbert function ([`crate::ff::hilbert::quotient_dimension`]).
    ///
    /// `Some(0)` for the whole ring, `Some(d)` for a zero-dimensional ideal,
    /// `None` when `R/I` is not finite-dimensional (positive-dimensional) or
    /// the dimension is declined for a pathologically large ideal. A pure
    /// combinatorial read of the finished basis (sound, verdict-neutral);
    /// cross-checks the FGLM staircase size in [`crate::gb::fglm`].
    pub fn quotient_dimension(&self) -> Option<u128> {
        if self.is_whole_ring() {
            return Some(0);
        }
        if self.basis.is_empty() {
            return None;
        }
        let ring = self.poly_ring.ctx();
        let n_vars = self.poly_ring.n_vars();
        let mut lead: Vec<Monomial> = Vec::with_capacity(self.basis.len());
        for p in &self.basis {
            if p.is_zero() {
                continue;
            }
            if let Some(lm) = p.leading_monomial(ring) {
                lead.push(lm);
            }
        }
        crate::ff::hilbert::quotient_dimension(&lead, n_vars)
    }

    /// Compute the minimal polynomial of `var_idx` in `R/I`.
    pub fn min_poly(&self, var_idx: usize) -> Option<Vec<FieldElem>> {
        self.min_poly_cancel(var_idx, &CancelToken::none())
    }

    /// Cancel-aware variant of [`Self::min_poly`].
    ///
    /// Computes the monic minimal polynomial of `x_{var_idx}` in `R/I`
    /// via Gaussian elimination on the normal forms of `1, x, x^2, ...`.
    /// Returns `None` if the ideal is not zero-dimensional or the search
    /// hits the degree cap.
    #[metric("ideal::min_poly")]
    pub fn min_poly_cancel(&self, var_idx: usize, cancel: &CancelToken) -> Option<Vec<FieldElem>> {
        let ring = self.poly_ring.ctx();
        let f = &ring.field;
        if self.is_whole_ring() { return Some(vec![f.one()]); }
        if !self.is_zero_dim() { return None; }

        let one_poly = Polynomial::constant(f.one(), ring);
        let x_poly = Polynomial::variable(var_idx, ring);
        let one_nf = self.reduce(&one_poly);
        let mut powers: Vec<Polynomial> = vec![one_nf];

        const MIN_POLY_DEG_CAP: usize = 4096;

        // Echelon form: each row is (normal_form, dependency vector).
        let mut nfs: Vec<Polynomial> = Vec::new();
        let mut deps: Vec<Vec<FieldElem>> = Vec::new();
        let mut pivot_monos: Vec<Monomial> = Vec::new();

        for d in 0..=MIN_POLY_DEG_CAP {
            if cancel.is_cancelled() { return None; }
            let nf = if d == 0 {
                powers[0].clone()
            } else {
                let prev = powers[d - 1].clone();
                let next = prev.mul(&x_poly, ring);
                self.reduce_with_cancel(&next, cancel)
            };
            // A cancelled reduction returns a partial (non-normal-form)
            // result; bail before it feeds the echelon step.
            if cancel.is_cancelled() {
                return None;
            }
            if d > 0 {
                powers.push(nf.clone());
            }

            // Build a row: (nf, e_d).
            let mut row_poly = nf.clone();
            let mut row_dep: Vec<FieldElem> = vec![f.zero(); d + 1];
            row_dep[d] = f.one();

            // Reduce row against existing echelon rows.
            for (i, nf_i) in nfs.iter().enumerate() {
                let lm_i = &pivot_monos[i];
                let coeff_at_lm = poly_coefficient_at(row_poly.as_dense(ring).as_ref(), lm_i, ring);
                if !f.is_zero(&coeff_at_lm) {
                    let lc_i = poly_coefficient_at(nf_i.as_dense(ring).as_ref(), lm_i, ring);
                    debug_assert!(!f.is_zero(&lc_i));
                    let factor = f.div(&coeff_at_lm, &lc_i).unwrap();
                    let neg_factor = f.neg(&factor);
                    let scaled = nf_i.scale(&neg_factor, ring);
                    row_poly = row_poly.add(&scaled, ring);
                    let dep_i = &deps[i];
                    debug_assert!(dep_i.len() <= row_dep.len(),
                        "echelon row dep length exceeds current row_dep");
                    for k in 0..dep_i.len() {
                        let prod = f.mul(&factor, &dep_i[k]);
                        f.sub_assign(&mut row_dep[k], &prod);
                    }
                }
            }

            if row_poly.is_zero() {
                // Found a dependency: normalise so the leading coefficient is 1.
                let mut top = row_dep.len();
                while top > 0 && f.is_zero(&row_dep[top - 1]) { top -= 1; }
                if top == 0 { return Some(vec![f.one()]); }
                let lead = row_dep[top - 1].clone();
                let mut coeffs: Vec<FieldElem> = Vec::with_capacity(top);
                for k in 0..top {
                    coeffs.push(f.div(&row_dep[k], &lead).unwrap());
                }
                return Some(coeffs);
            }

            // Add to echelon: pivot is the leading monomial of the (reduced) row.
            if let Some(lm) = row_poly.leading_monomial(ring) {
                pivot_monos.push(lm);
                nfs.push(row_poly);
                deps.push(row_dep);
            }
        }
        None
    }

    /// Divide `p` by its leading coefficient (in DegRevLex). LC becomes 1.
    pub fn normalize(&self, p: &Poly) -> Poly {
        if p.is_zero() { return Poly::zero(); }
        let ring = self.poly_ring.ctx();
        p.make_monic(ring)
    }
}

// ────────────────────── Standalone ring helpers ───────────────────────────

/// Get the leading monomial of a polynomial in a given monomial order.
///
/// The order parameter is accepted for API compatibility; the polynomial's
/// own ring already stores terms in canonical descending order
/// (`PolyRing.order`), so the first term's monomial is returned directly.
pub fn leading_monomial(
    ring: &PolyRingType,
    p: &Poly,
    _order: FfOrder,
) -> Option<Mono> {
    p.leading_monomial(&ring.ctx)
}

/// Get the leading coefficient of a polynomial in a given monomial order.
pub fn leading_coefficient(
    ring: &PolyRingType,
    p: &Poly,
    _order: FfOrder,
) -> FieldElem {
    match p.leading_coefficient() {
        Some(c) => ring.field().clone_el(c),
        None => ring.field().zero(),
    }
}

// ─────────────────────── interreduce_basis ────────────────────────────────

/// Interreduce a Groebner basis: replace each polynomial by its normal form
/// modulo the others, drop zeros, and monic-normalize. Output is the
/// *reduced* GB.
#[metric("ideal::interreduce")]
pub(crate) fn interreduce_basis(
    poly_ring: &FfPolyRing,
    basis: Vec<Poly>,
    cancel: &CancelToken,
) -> Vec<Poly> {
    if cancel.is_cancelled() {
        return basis;
    }
    if use_sparse_gb() {
        let ctx = poly_ring.ctx();
        let sparse: Vec<crate::ff::sparse_polynomial::SparsePolynomial> =
            basis.iter().map(|p| p.to_sparse(ctx)).collect();
        let reduced = crate::ff::sparse_gb::interreduce(sparse, ctx, Some(cancel));
        return reduced.into_iter().map(Poly::Sparse).collect();
    }
    wrap_dense_vec(buchberger::interreduce_with_cancel(
        unwrap_dense_vec(basis, poly_ring.ctx()),
        poly_ring.ctx(),
        Some(cancel),
    ))
}


#[cfg(test)]
mod tests;
