//! QF_FF equality atom interning. An atom is a canonical polynomial
//! `p = 0` over the prime field; equivalent equalities (e.g. `(= a b)`
//! and `(= b a)`) share one SAT variable. Disequalities reuse the
//! equality's variable via negative polarity.

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
    /// Canonical key for `(lhs = rhs)` mod `prime`. Negates `rhs`,
    /// normalizes, then sign-canonicalizes so the leading coefficient
    /// is in `[1, p/2]` — making `(= a b)` and `(= b a)` agree.
    pub fn from_eq(lhs: &[PolyTerm], rhs: &[PolyTerm], prime: &BigUint) -> Self {
        let mut polys: Vec<PolyTerm> = lhs.to_vec();
        for t in rhs {
            // Reduce mod prime first so un-reduced inputs do not underflow.
            let reduced = &t.coeff % prime;
            let neg_coeff = if reduced.is_zero() {
                BigUint::zero()
            } else {
                prime - &reduced
            };
            polys.push(PolyTerm {
                coeff: neg_coeff,
                vars: t.vars.clone(),
            });
        }
        crate::rewriter::normalize_term_list(&mut polys, prime);
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

    /// If this atom canonically pins one variable to a specific field
    /// constant (i.e. `a·x + c = 0` with `a ≠ 0` and `x` a single
    /// degree-1 variable), return `Some((var_name, value))` where
    /// `value` is the field element `x` must take: `−c · a⁻¹ mod p`.
    /// Used by [`AtomTable`] to emit at-most-one mutex clauses across
    /// atoms that constrain the same variable to different constants.
    ///
    /// Returns `None` for atoms with multiple variables, variables of
    /// degree > 1, or the trivial empty (`0 = 0`) polynomial. Since
    /// `prime` is prime, every non-zero coefficient is invertible, so
    /// we handle any non-zero `a` (not just `±1`).
    pub fn as_single_var_eq(&self, prime: &BigUint) -> Option<(String, BigUint)> {
        if self.terms.is_empty() {
            return None;
        }
        if self.terms.len() == 1 {
            let (coeff, vars) = &self.terms[0];
            if vars.len() != 1 || coeff.is_zero() {
                return None;
            }
            return Some((vars[0].clone(), BigUint::zero()));
        }
        if self.terms.len() != 2 {
            return None;
        }
        let (t0, t1) = (&self.terms[0], &self.terms[1]);
        let (var_term, const_term) = if t0.1.is_empty() {
            (t1, t0)
        } else if t1.1.is_empty() {
            (t0, t1)
        } else {
            return None;
        };
        if var_term.1.len() != 1 {
            return None;
        }
        let coeff_v = &var_term.0;
        let coeff_c = &const_term.0;
        if coeff_v.is_zero() {
            return None;
        }
        // a·v + c = 0  ⇒  v = (−c) · a⁻¹ mod p.  a⁻¹ via Fermat: a^(p−2).
        let neg_c = if coeff_c.is_zero() {
            BigUint::zero()
        } else {
            prime - coeff_c
        };
        let value = if coeff_v == &BigUint::from(1u32) {
            neg_c
        } else {
            let two = BigUint::from(2u32);
            if prime <= &two {
                return None;
            }
            let inv = coeff_v.modpow(&(prime - &two), prime);
            (neg_c * inv) % prime
        };
        Some((var_term.1[0].clone(), value))
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
    /// Tseitin auxiliaries have no AtomKey (`by_var[v] == None`).
    is_aux: Vec<bool>,
    /// `var_name -> [(value, atom_var)]` for single-variable equalities
    /// `±x = c`. Used by `intern_eq` to emit at-most-one mutex clauses.
    single_var_eq: HashMap<String, Vec<(BigUint, Var)>>,
}

impl AtomTable {
    pub fn new(prime: BigUint) -> Self {
        AtomTable {
            prime,
            by_key: HashMap::new(),
            by_var: Vec::new(),
            is_aux: Vec::new(),
            single_var_eq: HashMap::new(),
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
        if let Some((var_name, value)) = key.as_single_var_eq(&self.prime) {
            let entry = self.single_var_eq.entry(var_name).or_default();
            for (other_value, other_var) in entry.iter() {
                if other_value != &value {
                    sat.add_clause(vec![
                        crate::sat::Lit::neg(v),
                        crate::sat::Lit::neg(*other_var),
                    ]);
                }
            }
            entry.push((value, v));
        }
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

    /// Length of the variable-indexed atom slot vector. Callers iterate
    /// `0..n_atom_slots()` and use `atom(Var(i))` to skip aux slots.
    pub fn n_atom_slots(&self) -> usize {
        self.by_var.len()
    }

    /// Registered single-variable equalities for `var_name` as
    /// `(value, atom_var)` pairs in insertion order.
    pub fn atoms_for_var(&self, var_name: &str) -> &[(BigUint, Var)] {
        self.single_var_eq
            .get(var_name)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
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

    #[test]
    fn single_var_eq_detected() {
        let prime = BigUint::from(101u32);
        // `(= x 0)` → canonical key for `x = 0`.
        let k0 = AtomKey::from_eq(&[t(1, &["x"])], &[t(0, &[])], &prime);
        let (var, val) = k0.as_single_var_eq(&prime).expect("single-var-eq");
        assert_eq!(var, "x");
        assert_eq!(val, BigUint::zero());

        // `(= x 5)` → x = 5.
        let k5 = AtomKey::from_eq(&[t(1, &["x"])], &[t(5, &[])], &prime);
        let (var, val) = k5.as_single_var_eq(&prime).expect("single-var-eq");
        assert_eq!(var, "x");
        assert_eq!(val, BigUint::from(5u32));

        // `(= x y)` (two variables) → None.
        let kxy = AtomKey::from_eq(&[t(1, &["x"])], &[t(1, &["y"])], &prime);
        assert!(kxy.as_single_var_eq(&prime).is_none());

        // `(= (* x x) 0)` (degree 2) → None.
        let kxx = AtomKey::from_eq(&[t(1, &["x", "x"])], &[t(0, &[])], &prime);
        assert!(kxx.as_single_var_eq(&prime).is_none());
    }

    #[test]
    fn intern_eq_emits_mutex_clause_between_same_var_constants() {
        // Interning `(= x 0)` then `(= x 1)` should add a mutex clause
        // `(¬a0 ∨ ¬a1)` so SAT cannot assign both atoms True.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let a0 = match tbl.intern_eq(&[t(1, &["x"])], &[t(0, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let n_clauses_before = sat.n_clauses();
        let a1 = match tbl.intern_eq(&[t(1, &["x"])], &[t(1, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        assert_ne!(a0, a1);
        assert!(
            sat.n_clauses() > n_clauses_before,
            "interning (= x 1) after (= x 0) must emit at least one mutex clause"
        );
        // Assert both true at root → SAT becomes Unsat via the mutex.
        assert!(sat.add_clause(vec![Lit::pos(a0)]));
        let added_second = sat.add_clause(vec![Lit::pos(a1)]);
        assert!(!added_second);
        assert!(sat.is_unsat());
    }

    #[test]
    fn intern_eq_no_mutex_between_same_constant_repeats() {
        // Re-interning `(= x 0)` returns the same atom var; no extra
        // clause is added.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        tbl.intern_eq(&[t(1, &["x"])], &[t(0, &[])], &mut sat);
        let n_clauses_before = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(0, &[])], &mut sat);
        assert_eq!(sat.n_clauses(), n_clauses_before);
    }

    #[test]
    fn intern_eq_no_mutex_across_different_variables() {
        // `(= x 0)` and `(= y 0)` share no mutex; both atoms can be
        // True together.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let ax = match tbl.intern_eq(&[t(1, &["x"])], &[t(0, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let ay = match tbl.intern_eq(&[t(1, &["y"])], &[t(0, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        assert!(sat.add_clause(vec![Lit::pos(ax)]));
        assert!(sat.add_clause(vec![Lit::pos(ay)]));
        assert!(!sat.is_unsat());
    }

    #[test]
    fn intern_eq_emits_three_pairwise_mutexes_for_three_constants() {
        // Three atoms `(= x 0)`, `(= x 1)`, `(= x 2)` should produce
        // three pairwise mutex clauses (one per unordered pair).
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let n0 = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(0, &[])], &mut sat);
        let n1 = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(1, &[])], &mut sat);
        let n2 = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(2, &[])], &mut sat);
        let n3 = sat.n_clauses();
        assert_eq!(n1 - n0, 0, "first atom has nothing to mutex against");
        assert_eq!(n2 - n1, 1, "second atom mutexes with the first");
        assert_eq!(n3 - n2, 2, "third atom mutexes with both predecessors");
    }

    #[test]
    fn mutex_invariant_under_lhs_rhs_swap() {
        // `(= x 5)` and `(= 5 x)` canonicalize to the same atom, so
        // interning both should yield the same var and emit zero
        // additional clauses.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let r1 = tbl.intern_eq(&[t(1, &["x"])], &[t(5, &[])], &mut sat);
        let n_after_first = sat.n_clauses();
        let r2 = tbl.intern_eq(&[t(5, &[])], &[t(1, &["x"])], &mut sat);
        match (r1, r2) {
            (InternResult::Var(a), InternResult::Var(b)) => assert_eq!(a, b),
            _ => panic!("expected Var both times"),
        }
        assert_eq!(sat.n_clauses(), n_after_first, "no extra clause for canonical-duplicate");
    }

    #[test]
    fn single_var_eq_detects_nonunit_coefficient_via_fermat() {
        // Over GF(7): both `(= x 5)` and `(2x = 3)` solve to x = 5.
        let prime = BigUint::from(7u32);
        let k_direct = AtomKey::from_eq(&[t(1, &["x"])], &[t(5, &[])], &prime);
        let (var_d, val_d) = k_direct.as_single_var_eq(&prime).expect("direct");
        assert_eq!(var_d, "x");
        assert_eq!(val_d, BigUint::from(5u32));
        let k_scaled = AtomKey::from_eq(&[t(2, &["x"])], &[t(3, &[])], &prime);
        let (var_s, val_s) = k_scaled.as_single_var_eq(&prime).expect("scaled");
        assert_eq!(var_s, "x");
        assert_eq!(val_s, BigUint::from(5u32));
    }

    #[test]
    fn intern_eq_emits_mutex_across_semantically_distinct_scaled_atoms() {
        // Over GF(7): (= x 5) and (2x = 10) both pin x=5 but have
        // different canonical keys; no mutex between them. (= x 6) pins
        // x=6 and must mutex against both.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(7u32));
        let n0 = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(5, &[])], &mut sat);
        let n1 = sat.n_clauses();
        assert_eq!(n1 - n0, 0);
        tbl.intern_eq(&[t(2, &["x"])], &[t(10, &[])], &mut sat);
        let n2 = sat.n_clauses();
        assert_eq!(n2 - n1, 0, "x=5 again must not emit a mutex");
        tbl.intern_eq(&[t(1, &["x"])], &[t(6, &[])], &mut sat);
        let n3 = sat.n_clauses();
        assert_eq!(n3 - n2, 2, "x=6 mutexes against both x=5 atoms");
    }

    #[test]
    fn mutex_does_not_fire_for_equivalent_value_via_canonicalization() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(7u32));
        tbl.intern_eq(&[t(1, &["x"])], &[t(5, &[])], &mut sat);
        let n_after = sat.n_clauses();
        tbl.intern_eq(&[t(1, &["x"])], &[t(5, &[])], &mut sat);
        assert_eq!(sat.n_clauses(), n_after, "re-intern same atom: no clause");
        tbl.intern_eq(&[t(1, &["x"])], &[t(6, &[])], &mut sat);
        assert_eq!(sat.n_clauses(), n_after + 1, "x=6 mutexes with x=5");
    }
}
