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
mod tests {
    use super::*;

    #[test]
    fn lit_polarity_roundtrip() {
        let v = Var(7);
        let p = Lit::pos(v);
        let n = Lit::neg(v);
        assert_eq!(p.var(), v);
        assert_eq!(n.var(), v);
        assert!(p.is_positive());
        assert!(!n.is_positive());
        assert!(n.is_negative());
        assert_eq!(-p, n);
        assert_eq!(-n, p);
        assert_eq!(-(-p), p);
    }

    #[test]
    fn lit_index_disjoint_for_polarities() {
        let v = Var(3);
        let p = Lit::pos(v);
        let n = Lit::neg(v);
        assert_ne!(p.index(), n.index());
        assert_eq!(p.index(), 2 * v.index());
        assert_eq!(n.index(), 2 * v.index() + 1);
    }

    #[test]
    fn lbool_negation() {
        assert_eq!(LBool::True.negate(), LBool::False);
        assert_eq!(LBool::False.negate(), LBool::True);
        assert_eq!(LBool::Undef.negate(), LBool::Undef);
    }

    #[test]
    fn lbool_from_bool() {
        assert!(LBool::from_bool(true).is_true());
        assert!(LBool::from_bool(false).is_false());
    }

    #[test]
    fn lit_raw_roundtrip() {
        let v = Var(42);
        let p = Lit::pos(v);
        let n = Lit::neg(v);
        assert_eq!(Lit::from_raw(p.raw()), p);
        assert_eq!(Lit::from_raw(n.raw()), n);
    }
}
