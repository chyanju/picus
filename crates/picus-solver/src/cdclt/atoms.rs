//! Mapping between QF_FF atoms and SAT variables.
//!
//! An "atom" in this context is a polynomial equation `p = 0` over the
//! ambient prime field. Disequalities (`a ≠ b`) are NOT separate atoms;
//! they share the SAT variable of the corresponding equality and are
//! represented by negative literal polarity.
//!
//! Two SMT-LIB equalities that reduce to the same canonical polynomial
//! (e.g. `(= a b)` and `(= b a)`) share one SAT variable.

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::encoder::PolyTerm;
use crate::sat::{Lit, Solver, Var};

/// Canonical form of an equality atom: the term list of `lhs - rhs`
/// after `rewriter::normalize_term_list`. Two equalities are the
/// same atom iff their canonical keys are equal.
#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct AtomKey {
    /// Terms of the canonical polynomial. Each element is
    /// `(coefficient, sorted variable list)`. The list itself is
    /// sorted by `vars` (then by `coeff`), so equal atoms produce
    /// bit-identical keys.
    pub terms: Vec<(BigUint, Vec<String>)>,
}

impl AtomKey {
    /// Build the canonical key for `(lhs = rhs)` mod `prime`.
    ///
    /// `lhs = rhs` and `rhs = lhs` denote the same atom over GF(p)
    /// (the variety of `lhs − rhs = 0` equals the variety of
    /// `rhs − lhs = 0`). We pick a unique representative by flipping
    /// signs whenever the leading term's coefficient exceeds `p / 2`
    /// in symmetric-residue sense — guaranteeing that the leading
    /// coefficient is always in `[1, p/2]`.
    pub fn from_eq(lhs: &[PolyTerm], rhs: &[PolyTerm], prime: &BigUint) -> Self {
        let mut polys: Vec<PolyTerm> = lhs.to_vec();
        for t in rhs {
            let neg_coeff = if t.coeff.is_zero() {
                BigUint::zero()
            } else {
                prime - &t.coeff
            };
            polys.push(PolyTerm {
                coeff: neg_coeff,
                vars: t.vars.clone(),
            });
        }
        crate::rewriter::normalize_term_list(&mut polys, prime);
        // Canonicalize ± sign: if leading term's coeff > p/2, flip
        // every coefficient.
        if let Some(leading) = polys.first() {
            let half = prime / 2u32;
            if leading.coeff > half {
                for t in polys.iter_mut() {
                    if !t.coeff.is_zero() {
                        t.coeff = prime - &t.coeff;
                    }
                }
            }
        }
        AtomKey {
            terms: polys.into_iter().map(|t| (t.coeff, t.vars)).collect(),
        }
    }

    /// `true` when the canonical polynomial is the zero polynomial,
    /// i.e. the equality is `0 = 0` — trivially true.
    pub fn is_trivially_true(&self) -> bool {
        self.terms.is_empty()
    }

    /// Re-export the canonical polynomial as a `Vec<PolyTerm>` so the
    /// FF theory can feed it to the encoder.
    pub fn to_poly_terms(&self) -> Vec<PolyTerm> {
        self.terms
            .iter()
            .map(|(c, vs)| PolyTerm {
                coeff: c.clone(),
                vars: vs.clone(),
            })
            .collect()
    }
}

/// Interning table: maps canonical atom keys to SAT variables.
pub struct AtomTable {
    prime: BigUint,
    by_key: HashMap<AtomKey, Var>,
    by_var: Vec<Option<AtomKey>>,
    /// Variables introduced by Tseitin (auxiliaries). These have no
    /// AtomKey — `by_var[v.index()] == None`.
    is_aux: Vec<bool>,
}

impl AtomTable {
    pub fn new(prime: BigUint) -> Self {
        AtomTable {
            prime,
            by_key: HashMap::new(),
            by_var: Vec::new(),
            is_aux: Vec::new(),
        }
    }

    pub fn prime(&self) -> &BigUint {
        &self.prime
    }

    /// Allocate a fresh auxiliary SAT variable that has no associated
    /// atom (used by Tseitin transformations).
    pub fn new_aux(&mut self, sat: &mut Solver) -> Var {
        let v = sat.new_var();
        self.grow_to(v);
        self.is_aux[v.index()] = true;
        v
    }

    /// Intern an equality atom and return the SAT variable that
    /// represents it. Repeated calls with equivalent canonical
    /// polynomials return the same variable.
    ///
    /// Returns `None` for the trivial `0 = 0` case (caller must
    /// handle constant simplification upstream).
    pub fn intern_eq(
        &mut self,
        lhs: &[PolyTerm],
        rhs: &[PolyTerm],
        sat: &mut Solver,
    ) -> InternResult {
        let key = AtomKey::from_eq(lhs, rhs, &self.prime);
        if key.is_trivially_true() {
            return InternResult::Trivial(true);
        }
        if let Some(&v) = self.by_key.get(&key) {
            return InternResult::Var(v);
        }
        let v = sat.new_var();
        self.grow_to(v);
        self.by_key.insert(key.clone(), v);
        self.by_var[v.index()] = Some(key);
        self.is_aux[v.index()] = false;
        InternResult::Var(v)
    }

    /// Look up the canonical atom for a SAT variable. Returns `None`
    /// for auxiliary variables (Tseitin or other) and out-of-range
    /// indices.
    pub fn atom(&self, v: Var) -> Option<&AtomKey> {
        self.by_var.get(v.index()).and_then(|o| o.as_ref())
    }

    /// `true` iff `v` is a Tseitin / orchestration auxiliary
    /// variable rather than an FF atom.
    pub fn is_auxiliary(&self, v: Var) -> bool {
        self.is_aux.get(v.index()).copied().unwrap_or(false)
    }

    fn grow_to(&mut self, v: Var) {
        while self.by_var.len() <= v.index() {
            self.by_var.push(None);
            self.is_aux.push(false);
        }
    }
}

/// Outcome of an `intern_eq` call.
#[derive(Debug)]
pub enum InternResult {
    /// A SAT variable was returned. The positive literal denotes the
    /// equality holding; the negative literal denotes inequality.
    Var(Var),
    /// The equality is the constant `0 = 0` (trivially true) or its
    /// negation (trivially false), depending on caller polarity. The
    /// boolean carries the inherent truth value.
    Trivial(bool),
}

impl InternResult {
    /// Convert into a Lit assuming polarity-positive interpretation.
    /// Returns `Some(Lit::pos(v))` for a real atom; `None` for a
    /// trivially-true atom (caller must constant-fold).
    pub fn into_lit_pos(self) -> InternLit {
        match self {
            InternResult::Var(v) => InternLit::Lit(Lit::pos(v)),
            InternResult::Trivial(b) => InternLit::Constant(b),
        }
    }

    /// Same as `into_lit_pos` but with negative polarity (disequality).
    pub fn into_lit_neg(self) -> InternLit {
        match self {
            InternResult::Var(v) => InternLit::Lit(Lit::neg(v)),
            InternResult::Trivial(b) => InternLit::Constant(!b),
        }
    }
}

/// Helper enum used by the CNF builder: an atom interns to either a
/// real SAT literal or a constant truth value.
#[derive(Debug)]
pub enum InternLit {
    Lit(Lit),
    Constant(bool),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn intern_same_eq_returns_same_var() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let lhs = vec![t(1, &["x"])];
        let rhs = vec![t(0, &[])];
        let r1 = tbl.intern_eq(&lhs, &rhs, &mut sat);
        let r2 = tbl.intern_eq(&lhs, &rhs, &mut sat);
        match (r1, r2) {
            (InternResult::Var(v1), InternResult::Var(v2)) => assert_eq!(v1, v2),
            _ => panic!("expected two Var results"),
        }
        assert_eq!(sat.n_vars(), 1);
    }

    #[test]
    fn intern_symmetric_eq_dedups() {
        // (= x y) and (= y x) must share one var.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let lhs_a = vec![t(1, &["x"])];
        let rhs_a = vec![t(1, &["y"])];
        let lhs_b = vec![t(1, &["y"])];
        let rhs_b = vec![t(1, &["x"])];
        let r1 = tbl.intern_eq(&lhs_a, &rhs_a, &mut sat);
        let r2 = tbl.intern_eq(&lhs_b, &rhs_b, &mut sat);
        // After normalization both keys reduce to ±(x - y); the rewriter
        // canonicalizes one of these orderings.
        match (r1, r2) {
            (InternResult::Var(v1), InternResult::Var(v2)) => assert_eq!(v1, v2),
            _ => panic!("expected two Var results"),
        }
    }

    #[test]
    fn intern_trivial_eq() {
        // (= 0 0) → trivially true.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let lhs: Vec<PolyTerm> = vec![];
        let rhs: Vec<PolyTerm> = vec![];
        let r = tbl.intern_eq(&lhs, &rhs, &mut sat);
        match r {
            InternResult::Trivial(b) => assert!(b),
            _ => panic!("expected Trivial(true)"),
        }
        // No SAT var was allocated.
        assert_eq!(sat.n_vars(), 0);
    }

    #[test]
    fn aux_var_distinct_from_atom_var() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let lhs = vec![t(1, &["x"])];
        let rhs = vec![t(0, &[])];
        let r1 = tbl.intern_eq(&lhs, &rhs, &mut sat);
        let aux = tbl.new_aux(&mut sat);
        match r1 {
            InternResult::Var(v) => assert_ne!(v, aux),
            _ => panic!("expected Var"),
        }
        assert!(tbl.is_auxiliary(aux));
    }
}
