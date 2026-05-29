//! Propositional variables, literals, and three-valued logic.

/// A propositional variable, indexed from 0.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Var(pub u32);

impl Var {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A propositional literal: variable + polarity.
///
/// Encoded as `2 * var.index() | sign_bit`, with sign_bit = 0 for the
/// positive literal and 1 for the negative literal. This makes
/// negation a single XOR and lets a `Lit` index directly into per-
/// literal arrays sized `2 * n_vars`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct Lit(u32);

impl Lit {
    pub fn new(var: Var, positive: bool) -> Self {
        Lit((var.0 << 1) | (!positive as u32))
    }

    pub fn pos(var: Var) -> Self {
        Self::new(var, true)
    }

    pub fn neg(var: Var) -> Self {
        Self::new(var, false)
    }

    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    pub fn is_negative(self) -> bool {
        !self.is_positive()
    }

    pub fn raw(self) -> u32 {
        self.0
    }

    pub fn from_raw(raw: u32) -> Self {
        Lit(raw)
    }

    /// Index suitable for per-literal arrays (`watches[lit.index()]`).
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl std::ops::Neg for Lit {
    type Output = Lit;
    fn neg(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_negative() {
            write!(f, "-x{}", self.var().0)
        } else {
            write!(f, "x{}", self.var().0)
        }
    }
}

/// Three-valued logic: `True`, `False`, or `Undef`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum LBool {
    Undef,
    True,
    False,
}

impl LBool {
    pub fn from_bool(b: bool) -> Self {
        if b {
            LBool::True
        } else {
            LBool::False
        }
    }

    pub fn is_defined(self) -> bool {
        !matches!(self, LBool::Undef)
    }

    pub fn is_true(self) -> bool {
        matches!(self, LBool::True)
    }

    pub fn is_false(self) -> bool {
        matches!(self, LBool::False)
    }

    pub fn negate(self) -> LBool {
        match self {
            LBool::Undef => LBool::Undef,
            LBool::True => LBool::False,
            LBool::False => LBool::True,
        }
    }
}

#[cfg(test)]
#[path = "lit_tests.rs"]
mod tests;
