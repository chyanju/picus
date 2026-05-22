//! Solver-agnostic polynomial IR for propagation and (eventually)
//! backend lowering.
//!
//! A [`PolyIR`] bundles a polynomial ring over GF(p) together with the
//! constraint system extracted from a uniqueness query: a list of
//! `(poly = 0)` equalities, a list of `(p_1 = 0 ∨ p_2 = 0 ∨ ...)`
//! disjunctions, and bookkeeping about which wires are inputs / known /
//! the current uniqueness target.
//!
//! Variable layout. For an R1CS with `n_wires` wires, the ring carries
//! `2 * n_wires` variables. Variable index `i` (for `i < n_wires`) is
//! the original copy `x_i`; index `n_wires + i` is the alt copy `y_i`.
//! Inputs satisfy `x_i = y_i` (encoded as an explicit equality at
//! lowering time); wire 0 is the R1CS one-wire and pinned to `1` in
//! both copies. `target_signal` is the wire index `s` whose
//! uniqueness we are checking — equivalently, we ask whether
//! `x_s = y_s` is forced by the constraints.
//!
//! Propagation lemmas read the IR by reference; learned constraints are
//! pushed onto a separate buffer in the propagation context and are
//! folded into [`PolyIR::equalities`] by the DPVL outer loop at the end
//! of each fixed-point iteration.

use std::collections::HashSet;
use std::sync::Arc;

use num_bigint::BigUint;
use picus_r1cs::field_reduce;
use picus_r1cs::grammar::{ConstraintBlock, R1csFile};
use picus_solver::field::FfField;
use picus_solver::poly::{FfPolyRing, Poly};
use thiserror::Error;

/// Reasons the R1CS-to-PolyIR lowering can fail. Lowering used to
/// `log::warn!` + silently skip a malformed constraint block; the
/// resulting `PolyIR` was missing equalities the caller had no way to
/// detect, so any downstream verdict was untrustworthy. We now surface
/// the failure explicitly.
#[derive(Debug, Error)]
pub enum LowerError {
    #[error("wire id {wire} out of bounds (n_wires = {n_wires}) in {ctx}")]
    WireOutOfBounds {
        wire: usize,
        n_wires: usize,
        ctx: &'static str,
    },
}

/// Picus uniqueness query in polynomial form.
pub struct PolyIR {
    pub ring: Arc<FfPolyRing>,
    pub n_wires: usize,
    pub input_indices: HashSet<usize>,
    pub equalities: Vec<Poly>,
    pub disjunctions: Vec<Vec<Poly>>,
    /// Wires whose value is currently believed to be uniquely determined
    /// by the inputs. The DPVL loop seeds this with `input_indices`.
    pub known_signals: HashSet<usize>,
    /// Wire whose uniqueness we are testing this round; SAT means a
    /// witness pair exists where `x_target ≠ y_target`.
    pub target_signal: usize,
}

impl PolyIR {
    /// Index of the `x_i` variable in the underlying ring.
    pub fn orig_var(&self, wire: usize) -> usize {
        debug_assert!(wire < self.n_wires);
        wire
    }

    /// Index of the `y_i` variable in the underlying ring.
    pub fn alt_var(&self, wire: usize) -> usize {
        debug_assert!(wire < self.n_wires);
        self.n_wires + wire
    }

    /// Map a ring variable index back to its underlying wire index.
    /// `x_i` (index `i`) and `y_i` (index `n_wires + i`) both refer to
    /// the same wire `i` from a propagation standpoint, so callers
    /// pattern-matching on polynomial structure normally don't care
    /// which copy a variable belongs to.
    pub fn var_to_wire(&self, var: usize) -> usize {
        if var < self.n_wires {
            var
        } else {
            var - self.n_wires
        }
    }

    /// Canonical name for the original-copy variable of wire `wire`
    /// (e.g. `x5`).
    pub fn x_name(&self, wire: usize) -> &str {
        &self.ring.var_names[wire]
    }

    /// Canonical name for the alt-copy variable of wire `wire`
    /// (e.g. `y5`).
    pub fn y_name(&self, wire: usize) -> &str {
        &self.ring.var_names[self.n_wires + wire]
    }

    /// Build a `Poly` representing the linear polynomial `coeff * x` for
    /// variable index `var`. Used by lemmas that need to emit a learned
    /// constraint from a `(var, value)` pair.
    pub fn linear_term(&self, coeff: &BigUint, var: usize) -> Poly {
        let coeff_el = self.ring.field.from_biguint(coeff);
        self.ring.scale(coeff_el, self.ring.var(var))
    }

    /// Build a `Poly` representing the constant `c`.
    pub fn constant(&self, c: &BigUint) -> Poly {
        let el = self.ring.field.from_biguint(c);
        self.ring.constant(el)
    }

    /// Record that wire `w` has been proved unique by the DPVL outer
    /// loop. Appends `x_w - y_w = 0` to [`Self::equalities`] so the
    /// next backend call sees it as a regular constraint.
    pub fn add_known_wire(&mut self, w: usize) {
        if self.known_signals.insert(w) && !self.input_indices.contains(&w) {
            // Inputs already had `x_i - y_i = 0` baked in at lowering;
            // only non-input wires need a fresh equality here.
            let x = self.ring.var(self.orig_var(w));
            let y = self.ring.var(self.alt_var(w));
            self.equalities.push(self.ring.sub(x, y));
        }
    }

    /// Set the current uniqueness target. Does not mutate the
    /// constraint set; backends consume `target_signal` directly when
    /// emitting the closing disequality.
    pub fn set_target(&mut self, w: usize) {
        debug_assert!(w < self.n_wires);
        self.target_signal = w;
    }

    /// Iterate every term of `poly` as `(coeff, monomial_vars)`, where
    /// `monomial_vars` is a flat `Vec<String>` listing each variable's
    /// canonical name once per degree (e.g. `x*x` ⇒ `["x", "x"]`,
    /// `x*y` ⇒ `["x", "y"]`). Constant terms yield an empty `Vec`.
    /// Backends use this to translate the polynomial into their
    /// solver-native form.
    pub fn poly_terms<'a>(
        &'a self,
        poly: &'a Poly,
    ) -> impl Iterator<Item = (BigUint, Vec<String>)> + 'a {
        let ring = &self.ring.ring;
        let n_vars = ring.n_vars();
        let names = ring.var_names();
        ring.terms(poly).map(move |(coeff_el, m)| {
            let coeff = self.ring.field.to_biguint(coeff_el);
            let mut vars = Vec::new();
            for v in 0..n_vars {
                let e = ring.exponent_at(&m, v);
                for _ in 0..e {
                    vars.push(names[v].clone());
                }
            }
            (coeff, vars)
        })
    }
}

/// Construct a [`PolyIR`] from a parsed R1CS file. Performs the
/// equivalent of the old `expand_r1cs + normalize + optimize_p1` chain
/// in a single pass over the constraint blocks: each `A * B = C`
/// constraint becomes one polynomial equality `(sum_a)(sum_b) - sum_c =
/// 0`, with both copies (`x_i`, `y_i`) emitted side-by-side. Inputs are
/// pinned to a single value (`x_i - y_i = 0`); wire 0 is pinned to `1`
/// in both copies; the target signal disequality is *not* materialised
/// here (the GB solver handles it via a Rabinowitsch trick).
pub fn r1cs_to_poly_ir(
    r1cs: &R1csFile,
    known_signals: &HashSet<usize>,
    target_signal: usize,
) -> Result<PolyIR, LowerError> {
    let n_wires = r1cs.n_wires() as usize;
    let input_indices: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let prime = &r1cs.header.prime_number;

    // Build a ring with 2n variables: x_0..x_{n-1}, y_0..y_{n-1}.
    let mut var_names = Vec::with_capacity(2 * n_wires);
    for i in 0..n_wires {
        var_names.push(format!("x{}", i));
    }
    for i in 0..n_wires {
        var_names.push(format!("y{}", i));
    }
    let field = FfField::new(prime.clone());
    let ring = Arc::new(FfPolyRing::new(field, var_names));

    let mut equalities: Vec<Poly> = Vec::new();

    // Original-copy constraints.
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, /*is_alt=*/ false, prime)? {
            equalities.push(eq);
        }
    }
    // Alt-copy constraints.
    for c in &r1cs.constraints.constraints {
        if let Some(eq) = constraint_to_poly(&ring, &c.a, &c.b, &c.c, &input_indices, /*is_alt=*/ true, prime)? {
            equalities.push(eq);
        }
    }

    // Wire 0 pinned to 1. `block_to_linear` already folds `c * x_0`
    // straight into a constant, so the polynomials never reference
    // wire 0 — but backends still observe `x_0` as a ring variable
    // and need an equality to pin it. Wire 0 is an input, so the
    // alt copy collapses onto `x_0` in `block_to_linear` and `y_0`
    // is never referenced.
    let one_el = ring.field.one();
    equalities.push(ring.sub(ring.var(0), ring.constant(one_el)));

    // Inputs share their value across copies. `block_to_linear` emits
    // `x_i` (not `y_i`) for input wires in alt-copy constraints, so no
    // explicit `x_i - y_i = 0` equality is required: `y_i` for input
    // wires is simply never referenced.

    Ok(PolyIR {
        ring,
        n_wires,
        input_indices,
        equalities,
        disjunctions: Vec::new(),
        known_signals: known_signals.clone(),
        target_signal,
    })
}

/// Lower one R1CS constraint `A * B = C` into a polynomial equality
/// `expand(A) * expand(B) - expand(C) = 0` in the given copy. Returns
/// `Ok(None)` when the resulting polynomial is the zero polynomial,
/// `Err` when any block references an out-of-bounds wire id.
fn constraint_to_poly(
    ring: &Arc<FfPolyRing>,
    a: &ConstraintBlock,
    b: &ConstraintBlock,
    c: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
) -> Result<Option<Poly>, LowerError> {
    let sum_a = block_to_linear(ring, a, input_indices, is_alt, prime, "A")?;
    let sum_b = block_to_linear(ring, b, input_indices, is_alt, prime, "B")?;
    let sum_c = block_to_linear(ring, c, input_indices, is_alt, prime, "C")?;
    let ab = ring.mul(sum_a, sum_b);
    let eq = ring.sub(ab, sum_c);
    if ring.is_zero(&eq) {
        Ok(None)
    } else {
        Ok(Some(eq))
    }
}

/// Build the linear polynomial `sum_i coeff_i * var_i` for one R1CS
/// constraint block. Inputs use the original `x_i` index in both copies
/// (they share the same value); non-inputs use `x_i` in the orig copy
/// and `y_i` in the alt copy.
///
/// Wire 0 (the R1CS one-wire) is `1` by definition, so every
/// `coeff * x_0` term folds straight into the constant. Keeping the
/// fold here means the lemma layer sees `b * (b - 1) = 0` as
/// `b^2 - b = 0` rather than `b^2 + (p-1) * b * x_0 = 0`, and
/// pattern matchers like `binary01` don't need to track `x_0`
/// separately.
fn block_to_linear(
    ring: &Arc<FfPolyRing>,
    block: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
    prime: &BigUint,
    ctx: &'static str,
) -> Result<Poly, LowerError> {
    let n_wires = ring.n_vars / 2;
    let mut acc = ring.zero();
    for (&wire_id, factor) in block.wire_ids.iter().zip(block.factors.iter()) {
        let wid = wire_id as usize;
        if wid >= n_wires {
            return Err(LowerError::WireOutOfBounds {
                wire: wid,
                n_wires,
                ctx,
            });
        }
        let coeff = field_reduce(factor, prime);
        let coeff_el = ring.field.from_biguint(&coeff);
        let term = if wid == 0 {
            // x_0 = y_0 = 1 (R1CS one-wire); fold the coefficient
            // directly into the constant term so downstream
            // polynomials stay free of redundant `c * x_0` monomials.
            ring.constant(coeff_el)
        } else {
            let var_idx = if is_alt && !input_indices.contains(&wid) {
                n_wires + wid
            } else {
                wid
            };
            ring.scale(coeff_el, ring.var(var_idx))
        };
        acc = ring.add(acc, term);
    }
    Ok(acc)
}
