//! Encoder: translates a polynomial system into polynomials for GB computation.
//!
//! - Equality `f = 0` → polynomial `f`
//! - Disequality `a ≠ b` → Rabinowitsch trick: `(a - b) * w - 1`
//! - Bitsum subpatterns in equalities are extracted by
//!   [`auto_extract_bitsums`] and routed to `bitsum_polys`
//!   (split-GB basis 0 only).
//!
//! Single index-keyed type family. [`ConstraintSystem`] is the
//! canonical system shape (`var_names: Vec<String>` authoritative
//! for index↔name; equalities carry sparse `Vec<PolyTerm>` with
//! `(VarIdx, u16)` exponent pairs). [`ConstraintSystemBuilder`] is
//! the producer-side intern API; every public GB-query producer
//! (`native_ff` via `PolyIR::encode`, `smt2::parse` /
//! `parse_boolean`, `boolean::to_disjunct_systems`,
//! `cdclt::ff_theory`) constructs its output through a builder so
//! variable names are interned in encounter order with no
//! transient String-keyed struct ever materialised. The cache
//! ([`crate::incremental_context::IncrementalSolverContext`]) and
//! the `dump_smt` formatter both consume `ConstraintSystem`
//! directly.

use num_bigint::BigUint;
use std::collections::HashMap;

use crate::ff::field::PrimeField;
use crate::poly::{FfPolyRing, Poly};

/// Origin of an entry in [`EncodedSystem::polynomials`], parallel to it
/// 1:1. Lets a UNSAT-core consumer attribute a core polynomial index back
/// to the source constraint without relying on positional layout
/// assumptions. `Equality(j)` carries `j` = the index into the
/// `encode_impl`-input equality list; `Rabinowitsch(d)` carries `d` = the
/// index into the disequality list. `Other` is an encoder-introduced,
/// constraint-independent polynomial (the zero assignment, field
/// polynomials) that does not correspond to a removable source constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolySource {
    Equality(usize),
    Rabinowitsch(usize),
    Other,
}

/// Encoded polynomial system ready for GB computation.
pub struct EncodedSystem {
    pub poly_ring: FfPolyRing,
    pub polynomials: Vec<Poly>,
    /// Provenance of each `polynomials[k]`, same length and order.
    pub poly_provenance: Vec<PolySource>,
    /// Number of equalities `encode_impl` received (post-rewrite /
    /// post-bitsum-extraction). Equals the producer's pre-pipeline
    /// equality count iff `rewrite_system` dropped no equality; a
    /// core consumer uses this to decide whether `Equality(j)` indices
    /// align 1:1 with its own equality frame.
    pub n_input_equalities: usize,
    /// Bitsum definition polynomials: `b0 + 2*b1 + ... - aux = 0`.
    /// These are kept separate from `polynomials` because the split-GB
    /// algorithm seeds them only into the linear basis (basis 0), not
    /// the nonlinear basis (basis 1).
    pub bitsum_polys: Vec<Poly>,
    pub var_map: HashMap<String, usize>,
}



/// Divide a polynomial by its leading coefficient (in DegRevLex order).
fn normalize_poly(pr: &FfPolyRing, p: Poly) -> Poly {
    let ring = &pr.ring;
    let fp = &pr.field();
    if ring.is_zero(&p) || p.num_terms() == 0 { return p; }
    // Leading term is at index 0 (polynomials are stored sorted descending).
    let lc = fp.clone_el(p.leading_coefficient().expect("nonzero polynomial has a leading term"));
    if fp.is_zero(&lc) || fp.is_one(&lc) { return p; }
    let inv = fp.div(&fp.one(), &lc).expect("non-zero leading coefficient");
    let inv_poly = pr.constant(inv);
    ring.mul(inv_poly, p)
}

// ─────────────────────────────────────────────────────────────────────
//   Index-based constraint system
// ─────────────────────────────────────────────────────────────────────
//
// `ConstraintSystem` references variables by integer index into an
// owned `var_names` list, eliminating per-monomial String allocation
// and HashMap lookups in the encoder hot path. Producers build one via
// `ConstraintSystemBuilder`; `encode` is the entry point that turns it
// into polynomials.

/// Variable index into [`ConstraintSystem::var_names`]. `u32`
/// holds 4 G variables — well beyond any practical constraint
/// system.
pub type VarIdx = u32;

/// Ring index of the auxiliary variable for the `bitsum_i`-th bitsum,
/// given the user-variable count and the disequality count. Single source
/// of the encoder's auxiliary-variable layout: `encode_impl` appends, in
/// order, the user variables, then one Rabinowitsch witness per
/// disequality, then one `__bitsum_N` aux per bitsum. The bitsum extractor
/// must predict these indices before `encode_impl` allocates them, so both
/// sides route through this function and cannot drift.
pub(crate) fn bitsum_aux_index(n_user: usize, n_diseq: usize, bitsum_i: usize) -> VarIdx {
    (n_user + n_diseq + bitsum_i) as VarIdx
}

mod constraint_system;
pub use constraint_system::*;

mod bitsum_extract;
pub use bitsum_extract::*;

/// Encode a [`ConstraintSystem`] into polynomials.
///
/// Pre-encode pipeline:
///   1. `compact_used_vars`: drop variables from `var_names` that
///      no equality / disequality / assignment / bitsum references
///      — keeps the polynomial ring tight. Without this,
///      `PolyIR`'s `2 * n_wires` ring exposes every `y_i` even
///      when most are never referenced, inflating the GB engine's
///      monomial table and causing pathological slowdowns on big
///      circuits.
///   2. `rewriter::rewrite_system`: canonicalise terms.
///   3. `auto_extract_bitsums`: extract bitsum chains into
///      `bitsum_polys`.
pub fn encode(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::frontend::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, true)
}

/// Like [`encode`], but passes `emit_rabinowitsch = false` to
/// `encode_impl` so no Rabinowitsch witnesses are emitted for
/// disequalities.
pub fn encode_constraint_side(
    system: &ConstraintSystem,
) -> Result<EncodedSystem, String> {
    let compacted = compact_used_vars(system);
    let mut rewritten = compacted;
    crate::frontend::rewriter::rewrite_system(&mut rewritten);
    let extracted = auto_extract_bitsums(&rewritten);
    encode_impl(&extracted, false)
}

/// Compact `system.var_names` to only the variables actually
/// referenced by some equality, disequality, assignment, or
/// bitsum. Returns a new `ConstraintSystem` with renumbered
/// indices.
///
/// The ring must contain only variables that actually appear in the
/// constraint side; otherwise it gains spurious extra variables that
/// the GB engine has to factor in.
fn compact_used_vars(system: &ConstraintSystem) -> ConstraintSystem {
    use std::collections::BTreeSet;
    let mut used: BTreeSet<VarIdx> = BTreeSet::new();
    for eq in &system.equalities {
        for term in eq {
            for &(idx, _) in &term.vars {
                used.insert(idx);
            }
        }
    }
    for &(a, b) in &system.disequalities {
        used.insert(a);
        used.insert(b);
    }
    for (v, _) in &system.assignments {
        used.insert(*v);
    }
    for chain in &system.bitsums {
        for &v in chain {
            used.insert(v);
        }
    }
    if used.len() == system.var_names.len() {
        return system.clone();
    }
    let used_sorted: Vec<VarIdx> = used.into_iter().collect();
    let mut input_to_compact: HashMap<VarIdx, VarIdx> = HashMap::with_capacity(used_sorted.len());
    for (compact_idx, &input_idx) in used_sorted.iter().enumerate() {
        input_to_compact.insert(input_idx, compact_idx as VarIdx);
    }
    let new_var_names: Vec<String> = used_sorted
        .iter()
        .map(|&idx| system.var_names[idx as usize].clone())
        .collect();
    let new_equalities: Vec<Vec<PolyTerm>> = system
        .equalities
        .iter()
        .map(|eq| {
            eq.iter()
                .map(|t| PolyTerm {
                    coeff: t.coeff.clone(),
                    vars: t
                        .vars
                        .iter()
                        .map(|&(idx, exp)| (input_to_compact[&idx], exp))
                        .collect(),
                })
                .collect()
        })
        .collect();
    let new_disequalities: Vec<(VarIdx, VarIdx)> = system
        .disequalities
        .iter()
        .map(|&(a, b)| (input_to_compact[&a], input_to_compact[&b]))
        .collect();
    let new_assignments: Vec<(VarIdx, BigUint)> = system
        .assignments
        .iter()
        .map(|(v, val)| (input_to_compact[v], val.clone()))
        .collect();
    let new_bitsums: Vec<Vec<VarIdx>> = system
        .bitsums
        .iter()
        .map(|chain| chain.iter().map(|v| input_to_compact[v]).collect())
        .collect();
    ConstraintSystem {
        prime: system.prime.clone(),
        var_names: new_var_names,
        equalities: new_equalities,
        disequalities: new_disequalities,
        assignments: new_assignments,
        bitsums: new_bitsums,
        add_field_polys: system.add_field_polys,
    }
}

fn encode_impl(
    system: &ConstraintSystem,
    emit_rabinowitsch: bool,
) -> Result<EncodedSystem, String> {
    // Ring is `var_names` from the system, then aux witness vars for
    // disequalities and bitsums (one each, appended in order).
    let mut var_names: Vec<String> = system.var_names.clone();
    let n_user = var_names.len();

    let n_diseq = system.disequalities.len();
    let mut witness_idxs: Vec<VarIdx> = Vec::with_capacity(n_diseq);
    for i in 0..n_diseq {
        let name = format!("__w_diseq_{}", i);
        witness_idxs.push(var_names.len() as VarIdx);
        var_names.push(name);
    }

    let n_bitsum = system.bitsums.len();
    let mut bitsum_aux_idxs: Vec<VarIdx> = Vec::with_capacity(n_bitsum);
    for i in 0..n_bitsum {
        let name = format!("__bitsum_{}", i);
        // Derive the slot from the single-source layout formula the bitsum
        // extractor also uses to predict `__bitsum_N` references, so the
        // prediction and the allocation are the same expression and cannot
        // drift (in release too). The `__bitsum_i` name must land at exactly
        // this index for the slot to denote the variable it references.
        let slot = bitsum_aux_index(n_user, n_diseq, i);
        debug_assert_eq!(
            slot,
            var_names.len() as VarIdx,
            "bitsum aux append position drifted from bitsum_aux_index"
        );
        bitsum_aux_idxs.push(slot);
        var_names.push(name);
    }

    let n_vars = var_names.len();
    if n_vars > 5000 {
        return Err(format!(
            "too many variables ({}) for polynomial ring construction",
            n_vars
        ));
    }

    let field = PrimeField::new(system.prime.clone());
    let poly_ring = FfPolyRing::new(field, var_names.clone());

    // Build var_map for downstream callers that still consult it
    // (e.g. SUBP_CONSTANT_NAMES filtering in the picus crate).
    let mut var_map: HashMap<String, usize> = HashMap::with_capacity(n_vars);
    for (i, name) in var_names.iter().enumerate() {
        var_map.insert(name.clone(), i);
    }

    let mut polynomials: Vec<Poly> = Vec::new();
    // Parallel to `polynomials`: source constraint of each entry.
    let mut provenance: Vec<PolySource> = Vec::new();

    // Equalities: sum(coeff · prod_vars) = 0. Equality terms may
    // reference aux variables introduced by
    // `auto_extract_bitsums` (indices in the bitsum-aux
    // range); the bounds check is against the full ring size.
    let n_ring = var_names.len();
    for (eq_idx, eq) in system.equalities.iter().enumerate() {
        let mut poly = poly_ring.zero();
        for term in eq {
            let c = poly_ring.field().from_biguint(&term.coeff);
            let mut t = poly_ring.constant(c);
            for &(vidx, exp) in &term.vars {
                if (vidx as usize) >= n_ring {
                    return Err(format!(
                        "equality term references var_idx {} but ring has only {} vars",
                        vidx, n_ring
                    ));
                }
                let v_poly = poly_ring.var(vidx as usize);
                for _ in 0..exp {
                    t = poly_ring.mul(t, poly_ring.clone_poly(&v_poly));
                }
            }
            poly = poly_ring.add(poly, t);
        }
        if !poly_ring.is_zero(&poly) {
            polynomials.push(poly);
            provenance.push(PolySource::Equality(eq_idx));
        }
    }

    // Assignments: v - val = 0.
    for (v_idx, val) in &system.assignments {
        if (*v_idx as usize) >= n_user {
            return Err(format!(
                "assignment references var_idx {} but only {} user vars exist",
                v_idx, n_user
            ));
        }
        let v = poly_ring.var(*v_idx as usize);
        let c = poly_ring.constant(poly_ring.field().from_biguint(val));
        let diff = poly_ring.sub(v, c);
        if !poly_ring.is_zero(&diff) {
            polynomials.push(diff);
            provenance.push(PolySource::Other);
        }
    }

    // Rabinowitsch trick: (a - b) · w_i - 1 = 0 for each disequality.
    if emit_rabinowitsch {
        for (d_idx, ((a, b), &w_idx)) in
            system.disequalities.iter().zip(witness_idxs.iter()).enumerate()
        {
            if (*a as usize) >= n_user || (*b as usize) >= n_user {
                return Err(format!(
                    "disequality references var_idx >= {} but only {} user vars exist",
                    a.max(b),
                    n_user
                ));
            }
            let diff = poly_ring.sub(
                poly_ring.var(*a as usize),
                poly_ring.var(*b as usize),
            );
            let prod = poly_ring.mul(diff, poly_ring.var(w_idx as usize));
            let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
            polynomials.push(rabinowitsch);
            provenance.push(PolySource::Rabinowitsch(d_idx));
        }
    }

    // Bitsum definitions: b0 + 2·b1 + 4·b2 + ... - aux = 0.
    let mut bitsum_polys: Vec<Poly> = Vec::new();
    for (bs, &aux_idx) in system.bitsums.iter().zip(bitsum_aux_idxs.iter()) {
        let fp = &poly_ring.field();
        let two = fp.int_hom().map(2);
        let mut sum = poly_ring.zero();
        let mut coeff = poly_ring.field().one();
        for &bit_idx in bs {
            if (bit_idx as usize) >= n_user {
                return Err(format!(
                    "bitsum references var_idx {} but only {} user vars exist",
                    bit_idx, n_user
                ));
            }
            let term = poly_ring.scale(fp.clone_el(&coeff), poly_ring.var(bit_idx as usize));
            sum = poly_ring.add(sum, term);
            coeff = fp.mul_ref(&coeff, &two);
        }
        let aux = poly_ring.var(aux_idx as usize);
        let def_poly = poly_ring.sub(sum, aux);
        if !poly_ring.is_zero(&def_poly) {
            bitsum_polys.push(normalize_poly(&poly_ring, def_poly));
        }
    }

    // Field polynomials: x^p - x = 0 for every ring variable, emitted
    // only when `add_field_polys` is set and the prime is a single
    // u64 digit `<= 1000` (small enough for the dense `x^p` expansion).
    if system.add_field_polys {
        let p_usize = system.prime.to_u64_digits();
        if p_usize.len() == 1 && p_usize[0] <= 1000 {
            let p_val = p_usize[0] as usize;
            for i in 0..poly_ring.n_vars() {
                let x = poly_ring.var(i);
                let mut x_p = poly_ring.one();
                let mut base = poly_ring.clone_poly(&x);
                let mut exp = p_val;
                while exp > 0 {
                    if exp & 1 == 1 {
                        x_p = poly_ring.mul(x_p, poly_ring.clone_poly(&base));
                    }
                    base = poly_ring.mul(
                        poly_ring.clone_poly(&base),
                        poly_ring.clone_poly(&base),
                    );
                    exp >>= 1;
                }
                let field_poly = poly_ring.sub(x_p, x);
                if !poly_ring.is_zero(&field_poly) {
                    polynomials.push(field_poly);
                    provenance.push(PolySource::Other);
                }
            }
        }
    }

    debug_assert_eq!(
        provenance.len(),
        polynomials.len(),
        "poly_provenance must stay parallel to polynomials"
    );
    let polynomials = polynomials
        .into_iter()
        .map(|p| normalize_poly(&poly_ring, p))
        .collect();

    Ok(EncodedSystem {
        poly_ring,
        polynomials,
        poly_provenance: provenance,
        n_input_equalities: system.equalities.len(),
        bitsum_polys,
        var_map,
    })
}

#[cfg(test)]
#[path = "encoder_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "encoder_tests_spec.rs"]
mod tests_spec;
