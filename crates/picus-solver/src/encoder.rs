//! Encoder: translates a polynomial system into polynomials for GB computation.
//!
//! - Equality `f = 0` → polynomial `f`
//! - Disequality `a ≠ b` → Rabinowitsch trick: `(a - b) * w - 1`

use num_bigint::BigUint;
use std::collections::{HashMap, HashSet};

use feanor_math::homomorphism::*;
use feanor_math::ring::RingStore;

use crate::field::FfField;
use crate::ideal::leading_coefficient;
use crate::poly::{FfPolyRing, Poly};

/// Encoded polynomial system ready for GB computation.
pub struct EncodedSystem {
    pub poly_ring: FfPolyRing,
    pub polynomials: Vec<Poly>,
    /// Bitsum definition polynomials: `b0 + 2*b1 + ... - aux = 0`.
    /// These are kept separate from `polynomials` because the split-GB
    /// algorithm seeds them only into the linear basis (basis 0), not
    /// the nonlinear basis (basis 1).
    pub bitsum_polys: Vec<Poly>,
    pub var_map: HashMap<String, usize>,
}

/// A term in a polynomial constraint: coeff * prod(vars).
/// If vars is empty, it's a constant term.
#[derive(Clone, Debug)]
pub struct PolyTerm {
    pub coeff: BigUint,
    pub vars: Vec<String>,
}

/// Input constraint system.
pub struct ConstraintSystem {
    pub prime: BigUint,
    /// Each equality is a list of terms; their sum equals zero.
    pub equalities: Vec<Vec<PolyTerm>>,
    /// All disequalities: each pair (a, b) means `a ≠ b`.
    /// One Rabinowitsch witness variable per pair is introduced.
    pub disequalities: Vec<(String, String)>,
    /// Variable assignments: var = value.
    pub assignments: Vec<(String, BigUint)>,
    /// Whether to add field polynomials x^p - x for each variable.
    pub add_field_polys: bool,
    /// Optional bitsum declarations.  Each entry is a list of variable names
    /// `[b0, b1, ..., bk]` representing a bitsum `b0 + 2*b1 + 4*b2 + ...`.
    /// When provided, the encoder creates a fresh auxiliary variable for each
    /// bitsum and adds a definition polynomial `b0 + 2*b1 + ... - aux = 0`
    /// to a separate list (matching cvc5's `CocoaEncoder::bitsumPolys()`).
    /// When empty, the solver falls back to heuristic detection via `parse::bit_sums`.
    pub bitsums: Vec<Vec<String>>,
}

impl ConstraintSystem {
    /// Collect all variable names.
    pub fn collect_vars(&self) -> Vec<String> {
        let mut vars = HashSet::new();
        for eq in &self.equalities {
            for t in eq {
                for v in &t.vars {
                    vars.insert(v.clone());
                }
            }
        }
        for (v, _) in &self.assignments {
            vars.insert(v.clone());
        }
        for (a, b) in &self.disequalities {
            vars.insert(a.clone());
            vars.insert(b.clone());
        }
        for bs in &self.bitsums {
            for v in bs {
                vars.insert(v.clone());
            }
        }
        let mut sorted: Vec<_> = vars.into_iter().collect();
        sorted.sort();
        sorted
    }
}

/// Encode a constraint system into polynomials for GB computation.
pub fn encode(system: &ConstraintSystem) -> Result<EncodedSystem, String> {
    let mut var_names = system.collect_vars();

    // Add a Rabinowitsch witness variable for each disequality.
    let n_diseq = system.disequalities.len();
    let mut witness_vars: Vec<String> = Vec::with_capacity(n_diseq);
    for i in 0..n_diseq {
        let name = format!("__w_diseq_{}", i);
        var_names.push(name.clone());
        witness_vars.push(name);
    }

    // Add bitsum auxiliary variables.
    let mut bitsum_aux_vars: Vec<String> = Vec::with_capacity(system.bitsums.len());
    for i in 0..system.bitsums.len() {
        let name = format!("__bitsum_{}", i);
        var_names.push(name.clone());
        bitsum_aux_vars.push(name);
    }

    let field = FfField::new(&system.prime);
    let poly_ring = FfPolyRing::new(field, var_names.clone());

    let mut var_map: HashMap<String, usize> = HashMap::new();
    for (i, name) in var_names.iter().enumerate() {
        var_map.insert(name.clone(), i);
    }

    let mut polynomials = Vec::new();

    // Encode equalities: sum of (coeff * prod_vars) = 0
    for eq in &system.equalities {
        let mut poly = poly_ring.zero();
        for term in eq {
            let c = poly_ring.field.from_biguint(&term.coeff);
            let mut t = poly_ring.constant(c);
            for v in &term.vars {
                let idx = *var_map.get(v).ok_or_else(|| format!("unknown var: {}", v))?;
                t = poly_ring.mul(t, poly_ring.var(idx));
            }
            poly = poly_ring.add(poly, t);
        }
        if !poly_ring.is_zero(&poly) {
            polynomials.push(poly);
        }
    }

    // Encode assignments: var - value = 0
    for (var, val) in &system.assignments {
        let idx = *var_map.get(var).ok_or_else(|| format!("unknown var: {}", var))?;
        let v = poly_ring.var(idx);
        let c = poly_ring.constant(poly_ring.field.from_biguint(val));
        let diff = poly_ring.sub(v, c);
        if !poly_ring.is_zero(&diff) {
            polynomials.push(diff);
        }
    }

    // Rabinowitsch trick: (a - b) * w_i - 1 = 0 for each disequality.
    for ((a, b), w_name) in system.disequalities.iter().zip(witness_vars.iter()) {
        let a_idx = *var_map.get(a).ok_or_else(|| format!("unknown var: {}", a))?;
        let b_idx = *var_map.get(b).ok_or_else(|| format!("unknown var: {}", b))?;
        let w_idx = *var_map.get(w_name).unwrap();

        let diff = poly_ring.sub(poly_ring.var(a_idx), poly_ring.var(b_idx));
        let prod = poly_ring.mul(diff, poly_ring.var(w_idx));
        let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
        polynomials.push(rabinowitsch);
    }

    // Encode bitsum definitions: b0 + 2*b1 + 4*b2 + ... - aux = 0.
    // These go into a separate list (bitsum_polys) because the split-GB
    // algorithm seeds them only into the linear basis.
    let mut bitsum_polys = Vec::new();
    for (bs, aux_name) in system.bitsums.iter().zip(bitsum_aux_vars.iter()) {
        let fp = poly_ring.field.field();
        let two = fp.int_hom().map(2);
        let mut sum = poly_ring.zero();
        let mut coeff = poly_ring.field.one();
        for bit_var in bs {
            let idx = *var_map.get(bit_var).ok_or_else(|| format!("unknown bitsum var: {}", bit_var))?;
            let term = poly_ring.scale(fp.clone_el(&coeff), poly_ring.var(idx));
            sum = poly_ring.add(sum, term);
            coeff = fp.mul_ref(&coeff, &two);
        }
        let aux_idx = *var_map.get(aux_name).unwrap();
        let aux = poly_ring.var(aux_idx);
        let def_poly = poly_ring.sub(sum, aux);
        if !poly_ring.is_zero(&def_poly) {
            bitsum_polys.push(normalize_poly(&poly_ring, def_poly));
        }
    }

    // Optionally add field polynomials: x^p - x = 0 for each variable.
    if system.add_field_polys {
        let p_usize = system.prime.to_u64_digits();
        if p_usize.len() == 1 && p_usize[0] <= 1000 {
            let p_val = p_usize[0] as usize;
            for i in 0..poly_ring.n_vars {
                let x = poly_ring.var(i);
                // Compute x^p via repeated squaring
                let mut x_p = poly_ring.one();
                let mut base = poly_ring.clone_poly(&x);
                let mut exp = p_val;
                while exp > 0 {
                    if exp & 1 == 1 {
                        x_p = poly_ring.mul(x_p, poly_ring.clone_poly(&base));
                    }
                    base = poly_ring.mul(poly_ring.clone_poly(&base), poly_ring.clone_poly(&base));
                    exp >>= 1;
                }
                let field_poly = poly_ring.sub(x_p, x);
                if !poly_ring.is_zero(&field_poly) {
                    polynomials.push(field_poly);
                }
            }
        }
    }

    // Normalize all polynomials: divide by leading coefficient so LC = 1.
    // This matches cvc5's cocoa_encoder.cpp:326-329 and ensures consistent
    // representation for tracer-based UNSAT core extraction.
    let polynomials = polynomials.into_iter().map(|p| {
        normalize_poly(&poly_ring, p)
    }).collect();

    Ok(EncodedSystem { poly_ring, polynomials, bitsum_polys, var_map })
}

/// Divide a polynomial by its leading coefficient (in DegRevLex order).
fn normalize_poly(pr: &FfPolyRing, p: Poly) -> Poly {
    use feanor_math::rings::multivariate::DegRevLex;
    use feanor_math::ring::RingStore;
    use feanor_math::field::FieldStore;
    let ring = &pr.ring;
    let fp = pr.field.field();
    if ring.is_zero(&p) { return p; }
    let lc = leading_coefficient(ring, &p, DegRevLex);
    if fp.is_zero(&lc) || fp.is_one(&lc) { return p; }
    let inv = fp.div(&fp.one(), &lc);
    let inv_poly = pr.constant(inv);
    ring.mul(inv_poly, p)
}
