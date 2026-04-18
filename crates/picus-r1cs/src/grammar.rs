//! R1CS AST grammar types.

use num_bigint::BigUint;
use std::collections::HashSet;
use std::fmt;

// ============================================================
// Command-level AST
// ============================================================

/// A top-level list of commands.
#[derive(Debug, Clone)]
pub struct RCmds {
    pub commands: Vec<RCmd>,
}

/// A single command in the R1CS AST.
#[derive(Debug, Clone)]
pub enum RCmd {
    Raw(String),
    Logic(String),
    Def { var: String, typ: String },
    Assert(RExpr),
    Comment(String),
    Solve,
}

/// An expression node in the R1CS AST.
#[derive(Debug, Clone)]
pub enum RExpr {
    Int(BigUint),
    Var(String),
    Eq(Box<RExpr>, Box<RExpr>),
    Neq(Box<RExpr>, Box<RExpr>),
    Leq(Box<RExpr>, Box<RExpr>),
    Lt(Box<RExpr>, Box<RExpr>),
    Geq(Box<RExpr>, Box<RExpr>),
    Gt(Box<RExpr>, Box<RExpr>),
    And(Vec<RExpr>),
    Or(Vec<RExpr>),
    Imp(Box<RExpr>, Box<RExpr>),
    Add(Vec<RExpr>),
    Sub(Vec<RExpr>),
    Mul(Vec<RExpr>),
    Neg(Box<RExpr>),
    Mod(Box<RExpr>, Box<RExpr>),
}

impl RCmds {
    #[must_use]
    pub fn new(commands: Vec<RCmd>) -> Self {
        Self { commands }
    }

    #[must_use]
    pub fn empty() -> Self {
        Self {
            commands: Vec::new(),
        }
    }

    /// Concatenate multiple RCmds, consuming them.
    #[must_use]
    pub fn concat(parts: Vec<RCmds>) -> Self {
        let mut commands = Vec::new();
        for part in parts {
            commands.extend(part.commands);
        }
        Self { commands }
    }
}

// ============================================================
// Display
// ============================================================

impl fmt::Display for RExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RExpr::Int(v) => write!(f, "{}", v),
            RExpr::Var(v) => write!(f, "{}", v),
            RExpr::Eq(l, r) => write!(f, "{} = {}", l, r),
            RExpr::Neq(l, r) => write!(f, "{} != {}", l, r),
            RExpr::Leq(l, r) => write!(f, "{} <= {}", l, r),
            RExpr::Lt(l, r) => write!(f, "{} < {}", l, r),
            RExpr::Geq(l, r) => write!(f, "{} >= {}", l, r),
            RExpr::Gt(l, r) => write!(f, "{} > {}", l, r),
            RExpr::And(vs) => fmt_join(f, vs, " /\\ ", true),
            RExpr::Or(vs) => fmt_join(f, vs, " \\/ ", true),
            RExpr::Imp(l, r) => write!(f, "{} => {}", l, r),
            RExpr::Add(vs) => fmt_join(f, vs, " + ", false),
            RExpr::Sub(vs) => fmt_join(f, vs, " - ", false),
            RExpr::Mul(vs) => fmt_join(f, vs, " * ", false),
            RExpr::Neg(v) => write!(f, "(-{})", v),
            RExpr::Mod(v, _) => write!(f, "{}", v),
        }
    }
}

fn fmt_join(f: &mut fmt::Formatter<'_>, vs: &[RExpr], sep: &str, parens: bool) -> fmt::Result {
    for (i, v) in vs.iter().enumerate() {
        if i > 0 {
            write!(f, "{}", sep)?;
        }
        if parens {
            write!(f, "({})", v)?;
        } else {
            write!(f, "{}", v)?;
        }
    }
    Ok(())
}

// ============================================================
// Variable extraction
// ============================================================

/// Variable reference — either by name or index.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VarRef {
    Name(String),
    Index(usize),
}

/// Shared helpers for stripping mod wrappers and zero checks.
impl RExpr {
    /// Strip `Mod(inner, _)` wrapper, returning the inner expression.
    #[must_use]
    pub fn strip_mod(&self) -> &RExpr {
        if let RExpr::Mod(inner, _) = self {
            inner.as_ref()
        } else {
            self
        }
    }

    /// Check if this expression represents zero (possibly wrapped in Mod/Add).
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match self.strip_mod() {
            RExpr::Int(v) => v == &BigUint::ZERO,
            RExpr::Var(name) => name == "zero",
            RExpr::Add(vs) if vs.len() == 1 => vs[0].is_zero(),
            _ => false,
        }
    }

    /// Get all variable indices occurring in this expression.
    #[must_use]
    pub fn get_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_vars(&mut result, index_only, VarMode::All, false);
        result
    }

    /// Get variables that appear linearly (not in nonlinear multiplication).
    #[must_use]
    pub fn get_linear_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_vars(&mut result, index_only, VarMode::Linear, false);
        result
    }

    /// Get variables that appear nonlinearly.
    #[must_use]
    pub fn get_nonlinear_variables(&self, index_only: bool) -> HashSet<VarRef> {
        let mut result = HashSet::new();
        self.collect_vars(&mut result, index_only, VarMode::Nonlinear, false);
        result
    }

    /// Unified variable collector — replaces three separate recursive functions.
    fn collect_vars(
        &self,
        out: &mut HashSet<VarRef>,
        index_only: bool,
        mode: VarMode,
        include: bool,
    ) {
        match self {
            RExpr::Var(v) => {
                let should_add = match mode {
                    VarMode::All => {
                        v.starts_with('x') || v.starts_with('y')
                    }
                    VarMode::Linear => true,
                    VarMode::Nonlinear => include,
                };
                if should_add {
                    if index_only {
                        if let Some(idx) = crate::parse_var_index(v) {
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
                l.collect_vars(out, index_only, mode, include);
                r.collect_vars(out, index_only, mode, include);
            }
            RExpr::Mod(v, m) => {
                v.collect_vars(out, index_only, mode, include);
                m.collect_vars(out, index_only, mode, include);
            }
            RExpr::Neg(v) => v.collect_vars(out, index_only, mode, include),
            RExpr::And(vs) | RExpr::Or(vs) => {
                if mode == VarMode::Linear || mode == VarMode::Nonlinear {
                    // Not supported in linear/nonlinear context
                } else {
                    for v in vs {
                        v.collect_vars(out, index_only, mode, include);
                    }
                }
            }
            RExpr::Add(vs) | RExpr::Sub(vs) => {
                for v in vs {
                    v.collect_vars(out, index_only, mode, include);
                }
            }
            RExpr::Mul(vs) => {
                let var_count = vs.iter().filter(|e| matches!(e, RExpr::Var(_))).count();
                match mode {
                    VarMode::All => {
                        for v in vs {
                            v.collect_vars(out, index_only, mode, include);
                        }
                    }
                    VarMode::Linear => {
                        if var_count == 1 {
                            // Single var in product = linear
                            for v in vs.iter().filter(|e| matches!(e, RExpr::Var(_))) {
                                v.collect_vars(out, index_only, mode, include);
                            }
                        }
                    }
                    VarMode::Nonlinear => {
                        if var_count > 1 {
                            for v in vs.iter().filter(|e| matches!(e, RExpr::Var(_))) {
                                v.collect_vars(out, index_only, mode, true);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarMode {
    All,
    Linear,
    Nonlinear,
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
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
}

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

#[derive(Debug, Clone)]
pub struct ConstraintSection {
    pub constraints: Vec<Constraint>,
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub a: ConstraintBlock,
    pub b: ConstraintBlock,
    pub c: ConstraintBlock,
}

#[derive(Debug, Clone)]
pub struct ConstraintBlock {
    pub nnz: u32,
    pub wire_ids: Vec<u32>,
    pub factors: Vec<BigUint>,
}

#[derive(Debug, Clone)]
pub struct W2lSection {
    pub labels: Vec<u64>,
}

impl R1csFile {
    #[must_use]
    pub fn n_constraints(&self) -> u32 {
        self.header.m_constraints
    }

    #[must_use]
    pub fn n_wires(&self) -> u32 {
        self.header.n_wires
    }

    #[must_use]
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
