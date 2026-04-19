//! UniquenessQuery — solver-agnostic intermediate representation for a uniqueness check.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use picus_r1cs::grammar::{ConstraintBlock, R1csFile};
use picus_r1cs::{bn128_prime, field_reduce};
use std::collections::HashSet;

/// A complete uniqueness query ready for solving.
#[derive(Debug, Clone)]
pub struct UniquenessQuery {
    pub prime: BigUint,
    pub n_wires: usize,
    pub input_indices: HashSet<usize>,
    pub orig_constraints: Vec<IRConstraint>,
    pub alt_constraints: Vec<IRConstraint>,
    pub constants: Vec<(String, BigUint)>,
    pub known_signals: HashSet<usize>,
    pub target_signal: usize,
}

#[derive(Debug, Clone)]
pub enum IRConstraint {
    Linear(Vec<IRTerm>),
    NonLinear {
        lhs_terms: Vec<IRProductTerm>,
        rhs_terms: Vec<IRTerm>,
    },
    Or(Vec<IRConstraint>),
    VarEq(String, BigUint),
    VarNeq(String, String),
}

#[derive(Debug, Clone)]
pub struct IRTerm {
    pub coeff: BigUint,
    pub var: String,
}

#[derive(Debug, Clone)]
pub struct IRProductTerm {
    pub coeff: BigUint,
    pub var_a: String,
    pub var_b: String,
}

pub fn orig_var(index: usize) -> String {
    format!("x{}", index)
}

pub fn alt_var(index: usize, is_input: bool) -> String {
    if is_input { format!("x{}", index) } else { format!("y{}", index) }
}

/// Build a UniquenessQuery directly from an R1CS file.
///
/// This converts each R1CS constraint (A*B = C) into IR form:
/// - If A and B are both zero-blocks: linear constraint from C
/// - Otherwise: expanded cross-product (nonlinear)
pub fn build_query(
    r1cs: &R1csFile,
    known_signals: &HashSet<usize>,
    target_signal: usize,
) -> UniquenessQuery {
    let p = bn128_prime();
    let n_wires = r1cs.n_wires() as usize;
    let input_indices: HashSet<usize> = r1cs.inputs.iter().copied().collect();

    // Build constraints for original (x) and alternative (y) copies
    let orig_constraints = build_copy_constraints(r1cs, &input_indices, false);
    let alt_constraints = build_copy_constraints(r1cs, &input_indices, true);

    // Named constants (matching the SubP optimizer's convention)
    let constants = vec![
        ("ps1".into(), p - BigUint::one()),
        ("ps2".into(), p - BigUint::from(2u32)),
        ("ps3".into(), p - BigUint::from(3u32)),
        ("ps4".into(), p - BigUint::from(4u32)),
        ("ps5".into(), p - BigUint::from(5u32)),
        ("zero".into(), BigUint::zero()),
        ("one".into(), BigUint::one()),
    ];

    UniquenessQuery {
        prime: p.clone(),
        n_wires,
        input_indices,
        orig_constraints,
        alt_constraints,
        constants,
        known_signals: known_signals.clone(),
        target_signal,
    }
}

fn build_copy_constraints(
    r1cs: &R1csFile,
    input_indices: &HashSet<usize>,
    is_alt: bool,
) -> Vec<IRConstraint> {
    let mut constraints = Vec::new();

    for c in &r1cs.constraints.constraints {
        let a_terms = block_terms(&c.a, input_indices, is_alt);
        let b_terms = block_terms(&c.b, input_indices, is_alt);
        let c_terms = block_terms(&c.c, input_indices, is_alt);

        if a_terms.is_empty() && b_terms.is_empty() {
            // Linear: 0 = C → sum(c_terms) = 0
            if !c_terms.is_empty() {
                constraints.push(IRConstraint::Linear(c_terms));
            }
        } else {
            // Nonlinear: A*B = C → expand cross product
            let mut lhs = Vec::new();
            for at in &a_terms {
                for bt in &b_terms {
                    let coeff = field_reduce(&(&at.coeff * &bt.coeff));
                    if !coeff.is_zero() {
                        lhs.push(IRProductTerm {
                            coeff,
                            var_a: at.var.clone(),
                            var_b: bt.var.clone(),
                        });
                    }
                }
            }
            constraints.push(IRConstraint::NonLinear {
                lhs_terms: lhs,
                rhs_terms: c_terms,
            });
        }
    }

    constraints
}

fn block_terms(
    block: &ConstraintBlock,
    input_indices: &HashSet<usize>,
    is_alt: bool,
) -> Vec<IRTerm> {
    block
        .wire_ids
        .iter()
        .zip(block.factors.iter())
        .map(|(&wid, factor)| {
            let var = if is_alt {
                alt_var(wid as usize, input_indices.contains(&(wid as usize)))
            } else {
                orig_var(wid as usize)
            };
            IRTerm {
                coeff: factor.clone(),
                var,
            }
        })
        .collect()
}
