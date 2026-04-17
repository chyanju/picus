//! R1CS AST grammar types — a faithful translation of the Racket r1cs-grammar.rkt structs.
//!
//! This module defines:
//! 1. The **command-level AST** used to represent SMT-LIB-like constraint programs
//!    (definitions, assertions, logic connectives, arithmetic, etc.)
//! 2. The **binary R1CS structs** representing the iden3 R1CS file format.

use num_bigint::BigUint;
use std::collections::HashSet;
use std::fmt;

// ============================================================
// Command-level AST (the "r1cs grammar" used for SMT generation)
// ============================================================

/// A top-level list of commands.
#[derive(Debug, Clone)]
pub struct RCmds {
    pub vs: Vec<RCmd>,
}

/// A single command in the R1CS AST.
#[derive(Debug, Clone)]
pub enum RCmd {
    /// Raw solver-specific command string.
    Raw(String),
    /// Logic declaration (e.g., QF_NIA).
    Logic(String),
    /// Variable definition: `(declare-const var type)`.
    Def { var: String, typ: String },
    /// Assertion: `(assert ...)`.
    Assert(RExpr),
    /// Comment.
    Comment(String),
    /// `(check-sat)` + `(get-model)`.
    Solve,
}

/// An expression node in the R1CS AST.
#[derive(Debug, Clone)]
pub enum RExpr {
    /// Integer literal (may be very large, hence BigUint).
    Int(BigUint),
    /// Variable reference (e.g., "x0", "y3").
    Var(String),
    /// Equality: lhs = rhs.
    Eq(Box<RExpr>, Box<RExpr>),
    /// Inequality: lhs != rhs.
    Neq(Box<RExpr>, Box<RExpr>),
    /// Less-or-equal: lhs <= rhs.
    Leq(Box<RExpr>, Box<RExpr>),
    /// Less-than: lhs < rhs.
    Lt(Box<RExpr>, Box<RExpr>),
    /// Greater-or-equal: lhs >= rhs.
    Geq(Box<RExpr>, Box<RExpr>),
    /// Greater-than: lhs > rhs.
    Gt(Box<RExpr>, Box<RExpr>),
    /// Logical AND of multiple sub-expressions.
    And(Vec<RExpr>),
    /// Logical OR of multiple sub-expressions.
    Or(Vec<RExpr>),
    /// Implication: lhs => rhs.
    Imp(Box<RExpr>, Box<RExpr>),
    /// Addition of multiple sub-expressions.
    Add(Vec<RExpr>),
    /// Subtraction of multiple sub-expressions (left-associative).
    Sub(Vec<RExpr>),
    /// Multiplication of multiple sub-expressions.
    Mul(Vec<RExpr>),
    /// Negation: -v.
    Neg(Box<RExpr>),
    /// Modulo: v mod m.
    Mod(Box<RExpr>, Box<RExpr>),
}

impl RCmds {
    pub fn new(vs: Vec<RCmd>) -> Self {
        Self { vs }
    }

    pub fn empty() -> Self {
        Self { vs: Vec::new() }
    }

    /// Concatenate multiple RCmds into one.
    pub fn append(cmds: &[RCmds]) -> Self {
        let mut vs = Vec::new();
        for c in cmds {
            vs.extend(c.vs.iter().cloned());
        }
        Self { vs }
    }

    /// Get a human-readable string of the assertion at index `id`.
    pub fn to_string_at(&self, id: usize) -> String {
        self.vs[id].display_str()
    }
}

impl RCmd {
    fn display_str(&self) -> String {
        match self {
            RCmd::Raw(_) | RCmd::Logic(_) | RCmd::Def { .. } | RCmd::Comment(_) | RCmd::Solve => {
                String::new()
            }
            RCmd::Assert(e) => e.display_str(),
        }
    }
}

impl RExpr {
    fn display_str(&self) -> String {
        match self {
            RExpr::Int(v) => v.to_string(),
            RExpr::Var(v) => v.clone(),
            RExpr::Eq(l, r) => format!("{} = {}", l.display_str(), r.display_str()),
            RExpr::Neq(l, r) => format!("{} != {}", l.display_str(), r.display_str()),
            RExpr::Leq(l, r) => format!("{} <= {}", l.display_str(), r.display_str()),
            RExpr::Lt(l, r) => format!("{} < {}", l.display_str(), r.display_str()),
            RExpr::Geq(l, r) => format!("{} >= {}", l.display_str(), r.display_str()),
            RExpr::Gt(l, r) => format!("{} > {}", l.display_str(), r.display_str()),
            RExpr::And(vs) => vs
                .iter()
                .map(|v| format!("({})", v.display_str()))
                .collect::<Vec<_>>()
                .join(" /\\ "),
            RExpr::Or(vs) => vs
                .iter()
                .map(|v| format!("({})", v.display_str()))
                .collect::<Vec<_>>()
                .join(" \\/ "),
            RExpr::Imp(l, r) => format!("{} => {}", l.display_str(), r.display_str()),
            RExpr::Add(vs) => vs
                .iter()
                .map(|v| v.display_str())
                .collect::<Vec<_>>()
                .join(" + "),
            RExpr::Sub(vs) => vs
                .iter()
                .map(|v| v.display_str())
                .collect::<Vec<_>>()
                .join(" - "),
            RExpr::Mul(vs) => vs
                .iter()
                .map(|v| v.display_str())
                .collect::<Vec<_>>()
                .join(" * "),
            RExpr::Neg(v) => format!("(-{})", v.display_str()),
            RExpr::Mod(v, _m) => v.display_str(),
        }
    }
}

impl fmt::Display for RExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_str())
    }
}

// ============================================================
// Variable extraction utilities (matching r1cs-grammar.rkt)
// ============================================================

impl RExpr {
    /// Get all variable indices occurring in this expression.
    /// If `index_only` is true, returns numeric indices (e.g., "x3" → 3).
    /// Variables must start with 'x' or 'y'.
    pub fn get_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_variables(&mut result, index_only);
        result
    }

    /// Get variables that appear linearly (not in a nonlinear multiplication).
    /// In `rmul`, only single-variable products count as linear.
    pub fn get_linear_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_linear_variables(&mut result, index_only);
        result
    }

    /// Get variables that appear nonlinearly (in a multiplication with another variable).
    pub fn get_nonlinear_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_nonlinear_variables(&mut result, index_only, false);
        result
    }

    fn collect_variables(&self, out: &mut HashSet<VarRef>, index_only: bool) {
        match self {
            RExpr::Var(v) => {
                if v.starts_with('x') || v.starts_with('y') {
                    if index_only {
                        if let Ok(idx) = v[1..].parse::<usize>() {
                            out.insert(VarRef::Index(idx));
                        }
                    } else {
                        out.insert(VarRef::Name(v.clone()));
                    }
                }
            }
            RExpr::Int(_) => {}
            RExpr::Eq(l, r)
            | RExpr::Neq(l, r)
            | RExpr::Leq(l, r)
            | RExpr::Lt(l, r)
            | RExpr::Geq(l, r)
            | RExpr::Gt(l, r)
            | RExpr::Imp(l, r)
            | RExpr::Mod(l, r) => {
                l.collect_variables(out, index_only);
                r.collect_variables(out, index_only);
            }
            RExpr::And(vs) | RExpr::Or(vs) | RExpr::Add(vs) | RExpr::Sub(vs) | RExpr::Mul(vs) => {
                for v in vs {
                    v.collect_variables(out, index_only);
                }
            }
            RExpr::Neg(v) => v.collect_variables(out, index_only),
        }
    }

    fn collect_linear_variables(&self, out: &mut HashSet<VarRef>, index_only: bool) {
        match self {
            RExpr::Var(v) => {
                if index_only {
                    if let Ok(idx) = v[1..].parse::<usize>() {
                        out.insert(VarRef::Index(idx));
                    }
                } else {
                    out.insert(VarRef::Name(v.clone()));
                }
            }
            RExpr::Int(_) => {}
            RExpr::Eq(l, r)
            | RExpr::Neq(l, r)
            | RExpr::Leq(l, r)
            | RExpr::Lt(l, r)
            | RExpr::Geq(l, r)
            | RExpr::Gt(l, r)
            | RExpr::Imp(l, r) => {
                l.collect_linear_variables(out, index_only);
                r.collect_linear_variables(out, index_only);
            }
            RExpr::And(_) | RExpr::Or(_) => {
                // Not supported in linear context per original code
            }
            RExpr::Add(vs) | RExpr::Sub(vs) => {
                for v in vs {
                    v.collect_linear_variables(out, index_only);
                }
            }
            RExpr::Mul(vs) => {
                // Only linear if exactly one variable in the product
                let vars: Vec<&RExpr> = vs.iter().filter(|e| matches!(e, RExpr::Var(_))).collect();
                if vars.len() == 1 {
                    vars[0].collect_linear_variables(out, index_only);
                }
                // else: more than 1 var → nonlinear, return nothing
            }
            RExpr::Mod(v, m) => {
                v.collect_linear_variables(out, index_only);
                m.collect_linear_variables(out, index_only);
            }
            RExpr::Neg(v) => v.collect_linear_variables(out, index_only),
        }
    }

    fn collect_nonlinear_variables(
        &self,
        out: &mut HashSet<VarRef>,
        index_only: bool,
        include: bool,
    ) {
        match self {
            RExpr::Var(v) => {
                if include {
                    if index_only {
                        if let Ok(idx) = v[1..].parse::<usize>() {
                            out.insert(VarRef::Index(idx));
                        }
                    } else {
                        out.insert(VarRef::Name(v.clone()));
                    }
                }
            }
            RExpr::Int(_) => {}
            RExpr::Eq(l, r)
            | RExpr::Neq(l, r)
            | RExpr::Leq(l, r)
            | RExpr::Lt(l, r)
            | RExpr::Geq(l, r)
            | RExpr::Gt(l, r)
            | RExpr::Imp(l, r) => {
                l.collect_nonlinear_variables(out, index_only, include);
                r.collect_nonlinear_variables(out, index_only, include);
            }
            RExpr::And(_) | RExpr::Or(_) => {}
            RExpr::Add(vs) | RExpr::Sub(vs) => {
                for v in vs {
                    v.collect_nonlinear_variables(out, index_only, include);
                }
            }
            RExpr::Mul(vs) => {
                let vars: Vec<&RExpr> = vs.iter().filter(|e| matches!(e, RExpr::Var(_))).collect();
                if vars.len() > 1 {
                    // Nonlinear: include all vars
                    for v in &vars {
                        v.collect_nonlinear_variables(out, index_only, true);
                    }
                }
                // else: 0 or 1 var → linear, do nothing
            }
            RExpr::Mod(v, m) => {
                v.collect_nonlinear_variables(out, index_only, include);
                m.collect_nonlinear_variables(out, index_only, include);
            }
            RExpr::Neg(v) => v.collect_nonlinear_variables(out, index_only, include),
        }
    }
}

/// Variable reference - either by name ("x3") or by index (3).
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VarRef {
    Name(String),
    Index(usize),
}

// ============================================================
// Binary R1CS file structs
// ============================================================

/// A parsed R1CS file.
#[derive(Debug, Clone)]
pub struct R1csFile {
    pub magic: [u8; 4],
    pub version: u32,
    pub n_sections: u32,
    pub header: HeaderSection,
    pub constraints: ConstraintSection,
    pub w2l: W2lSection,
    /// 0-based input signal indices (includes wire 0 = constant 1).
    pub inputs: Vec<usize>,
    /// 0-based output signal indices.
    pub outputs: Vec<usize>,
}

/// Header section of an R1CS file.
#[derive(Debug, Clone)]
pub struct HeaderSection {
    pub field_size: u32,
    pub prime_number: BigUint,
    pub n_wires: u32,
    pub n_pub_out: u32,
    pub n_pub_in: u32,
    pub n_prv_in: u32,
    pub n_labels: u64,
    pub m_constraints: u32,
}

/// Constraint section: a list of constraints.
#[derive(Debug, Clone)]
pub struct ConstraintSection {
    pub constraints: Vec<Constraint>,
}

/// A single R1CS constraint: A * B = C.
#[derive(Debug, Clone)]
pub struct Constraint {
    pub a: ConstraintBlock,
    pub b: ConstraintBlock,
    pub c: ConstraintBlock,
}

/// One block (A, B, or C) of a constraint: sparse linear combination.
#[derive(Debug, Clone)]
pub struct ConstraintBlock {
    pub nnz: u32,
    pub wire_ids: Vec<u32>,
    pub factors: Vec<BigUint>,
}

/// Wire-to-label mapping section.
#[derive(Debug, Clone)]
pub struct W2lSection {
    pub labels: Vec<u64>,
}

impl R1csFile {
    pub fn n_constraints(&self) -> u32 {
        self.header.m_constraints
    }

    pub fn n_wires(&self) -> u32 {
        self.header.n_wires
    }

    /// Get a human-readable string of constraint at index `id`.
    pub fn constraint_to_string(&self, id: usize) -> String {
        let c = &self.constraints.constraints[id];

        let block_str = |b: &ConstraintBlock| -> String {
            if b.nnz == 0 {
                return "0".to_string();
            }
            b.wire_ids
                .iter()
                .zip(b.factors.iter())
                .map(|(w, f)| format!("({} * x{})", f, w))
                .collect::<Vec<_>>()
                .join(" + ")
        };

        format!(
            "( {} ) * ( {} ) = {}",
            block_str(&c.a),
            block_str(&c.b),
            block_str(&c.c)
        )
    }
}
