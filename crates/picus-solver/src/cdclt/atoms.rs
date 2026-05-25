//! QF_FF equality atom interning. An atom is a canonical polynomial
//! `p = 0` over the prime field; equivalent equalities (e.g. `(= a b)`
//! and `(= b a)`) share one SAT variable. Disequalities reuse the
//! equality's variable via negative polarity.
//!
//! `AtomKey` is the long-lived cache key used by the SAT layer to
//! dedup semantically equivalent equalities across `ff_theory`
//! `post_check` calls. Because each `post_check` rebuilds a fresh
//! `ConstraintSystemBuilder` from the trail, polynomial-ring variable
//! indices are not stable across calls — so the cache key here is
//! kept in name-keyed form (`Vec<(BigUint, Vec<String>)>`) rather
//! than the index-keyed `PolyTerm`. Callers feeding equalities into
//! the atom table pass `Vec<PolyTerm>` plus the producing builder's
//! `var_names` slice; [`AtomKey::from_indexed_eq`] reverse-resolves
//! the names internally.

use std::collections::{BTreeMap, HashMap};

use num_bigint::BigUint;
use num_traits::Zero;

use crate::frontend::encoder::{ConstraintSystemBuilder, PolyTerm, VarIdx};
use crate::sat::{Lit, Solver, Var};

/// Normalize a name-keyed term list in place. Within-term `vars`
/// sort, like-term coefficient sum mod `prime`, drop of zero-coeff
/// terms. Mirrors [`crate::frontend::rewriter::normalize_term_list`]
/// for the AST-scratch form `AtomKey` uses internally.
fn normalize_named_terms(terms: &mut Vec<(BigUint, Vec<String>)>, prime: &BigUint) {
    for (coeff, vars) in terms.iter_mut() {
        vars.sort();
        *coeff = &*coeff % prime;
    }
    terms.sort_by(|a, b| a.1.cmp(&b.1).then(a.0.cmp(&b.0)));
    let mut out: Vec<(BigUint, Vec<String>)> = Vec::with_capacity(terms.len());
    for (coeff, vars) in terms.drain(..) {
        if let Some(last) = out.last_mut() {
            if last.1 == vars {
                last.0 = (&last.0 + &coeff) % prime;
                continue;
            }
        }
        out.push((coeff, vars));
    }
    out.retain(|(c, _)| !c.is_zero());
    *terms = out;
}

/// Canonical form of an equality atom: the term list of `lhs - rhs`
/// after [`normalize_named_terms`]. Two equalities are the
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
    /// Canonical key for `(lhs = rhs)` mod `prime`, where `lhs` and
    /// `rhs` are index-keyed `Vec<PolyTerm>` and `var_names` is the
    /// producing builder's frame. Reverse-resolves indices to names,
    /// negates `rhs`, normalizes, then sign-canonicalizes so the
    /// leading coefficient is in `[1, p/2]` — making `(= a b)` and
    /// `(= b a)` agree across producers.
    pub fn from_indexed_eq(
        lhs: &[PolyTerm],
        rhs: &[PolyTerm],
        var_names: &[String],
        prime: &BigUint,
    ) -> Self {
        let resolve = |t: &PolyTerm| -> (BigUint, Vec<String>) {
            let mut names: Vec<String> = Vec::with_capacity(
                t.vars.iter().map(|&(_, exp)| exp as usize).sum(),
            );
            for &(idx, exp) in &t.vars {
                let name = &var_names[idx as usize];
                for _ in 0..exp {
                    names.push(name.clone());
                }
            }
            (&t.coeff % prime, names)
        };
        let mut polys: Vec<(BigUint, Vec<String>)> =
            lhs.iter().map(&resolve).collect();
        for t in rhs {
            let (coeff, vars) = resolve(t);
            let neg_coeff = if coeff.is_zero() {
                BigUint::zero()
            } else {
                prime - coeff
            };
            polys.push((neg_coeff, vars));
        }
        normalize_named_terms(&mut polys, prime);
        if let Some((leading, _)) = polys.first() {
            let half = prime / 2u32;
            if leading > &half {
                for (c, _) in polys.iter_mut() {
                    if !c.is_zero() {
                        *c = prime - &*c;
                    }
                }
            }
        }
        AtomKey { terms: polys }
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

    /// Intern this atom's canonical polynomial into `builder`,
    /// returning the index-keyed `Vec<PolyTerm>` ready to feed to
    /// `builder.add_equality`. Within-term repeated names
    /// (`x * x` as `vars = ["x", "x"]`) collapse to a sparse
    /// `(VarIdx, 2)` exponent pair.
    pub fn intern_into(&self, builder: &mut ConstraintSystemBuilder) -> Vec<PolyTerm> {
        self.terms
            .iter()
            .map(|(coeff, names)| {
                let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
                for v in names {
                    let idx = builder.var(v);
                    *counts.entry(idx).or_insert(0) += 1;
                }
                PolyTerm {
                    coeff: coeff.clone(),
                    vars: counts.into_iter().collect(),
                }
            })
            .collect()
    }

    /// Intern the negation of this atom's polynomial into `builder`.
    /// Used by `ff_theory` to assemble the Rabinowitsch trick body
    /// `d - lhs = 0`, where `-lhs` is the negated atom polynomial.
    pub fn intern_negated_into(
        &self,
        builder: &mut ConstraintSystemBuilder,
        prime: &BigUint,
    ) -> Vec<PolyTerm> {
        self.terms
            .iter()
            .map(|(coeff, names)| {
                let mut counts: BTreeMap<VarIdx, u16> = BTreeMap::new();
                for v in names {
                    let idx = builder.var(v);
                    *counts.entry(idx).or_insert(0) += 1;
                }
                let neg = if coeff.is_zero() {
                    BigUint::zero()
                } else {
                    prime - coeff
                };
                PolyTerm {
                    coeff: neg,
                    vars: counts.into_iter().collect(),
                }
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
    /// Inputs are index-keyed `&[PolyTerm]` over the builder's
    /// `var_names` frame; the atom table reverse-resolves names
    /// internally to build the name-keyed cache key. Returns
    /// `Trivial(true)` for the constant `0 = 0` case.
    pub fn intern_eq(
        &mut self,
        lhs: &[PolyTerm],
        rhs: &[PolyTerm],
        var_names: &[String],
        sat: &mut Solver,
    ) -> InternResult {
        let key = AtomKey::from_indexed_eq(lhs, rhs, var_names, &self.prime);
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
    use crate::frontend::encoder::VarIdx;

    /// Index-keyed term constructor for tests. `idx_vars` is a list
    /// of `(VarIdx, exp)` pairs.
    fn pt(coeff: u64, idx_vars: &[(VarIdx, u16)]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: idx_vars.to_vec(),
        }
    }

    /// Construct a single-name-keyed term list `coeff * x` for var
    /// index 0 (the test's only variable). `vars = &[]` yields a
    /// constant term.
    fn t(coeff: u64, exp: u16) -> PolyTerm {
        if exp == 0 {
            pt(coeff, &[])
        } else {
            pt(coeff, &[(0, exp)])
        }
    }

    fn names(ns: &[&str]) -> Vec<String> {
        ns.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn intern_same_eq_returns_same_var() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        let lhs = vec![t(1, 1)];
        let rhs = vec![t(0, 0)];
        let r1 = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
        let r2 = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
        match (r1, r2) {
            (InternResult::Var(v1), InternResult::Var(v2)) => assert_eq!(v1, v2),
            _ => panic!("expected two Var results"),
        }
        assert_eq!(sat.n_vars(), 1);
    }

    #[test]
    fn intern_symmetric_eq_dedups() {
        // (= x y) and (= y x) must share one var.
        // var index 0 = x, index 1 = y.
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x", "y"]);
        let lhs_a = vec![pt(1, &[(0, 1)])]; // x
        let rhs_a = vec![pt(1, &[(1, 1)])]; // y
        let lhs_b = vec![pt(1, &[(1, 1)])]; // y
        let rhs_b = vec![pt(1, &[(0, 1)])]; // x
        let r1 = tbl.intern_eq(&lhs_a, &rhs_a, &vn, &mut sat);
        let r2 = tbl.intern_eq(&lhs_b, &rhs_b, &vn, &mut sat);
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
        let vn: Vec<String> = vec![];
        let lhs: Vec<PolyTerm> = vec![];
        let rhs: Vec<PolyTerm> = vec![];
        let r = tbl.intern_eq(&lhs, &rhs, &vn, &mut sat);
        match r {
            InternResult::Trivial(b) => assert!(b),
            _ => panic!("expected Trivial(true)"),
        }
        assert_eq!(sat.n_vars(), 0);
    }

    #[test]
    fn aux_var_distinct_from_atom_var() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        let r1 = tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
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
        let vn = names(&["x"]);
        // `(= x 0)` → canonical key for `x = 0`.
        let k0 = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(0, 0)], &vn, &prime);
        let (var, val) = k0.as_single_var_eq(&prime).expect("single-var-eq");
        assert_eq!(var, "x");
        assert_eq!(val, BigUint::zero());

        // `(= x 5)` → x = 5.
        let k5 = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(5, 0)], &vn, &prime);
        let (var, val) = k5.as_single_var_eq(&prime).expect("single-var-eq");
        assert_eq!(var, "x");
        assert_eq!(val, BigUint::from(5u32));

        // `(= x y)` (two variables) → None.
        let vn_xy = names(&["x", "y"]);
        let kxy = AtomKey::from_indexed_eq(
            &[pt(1, &[(0, 1)])],
            &[pt(1, &[(1, 1)])],
            &vn_xy,
            &prime,
        );
        assert!(kxy.as_single_var_eq(&prime).is_none());

        // `(= (* x x) 0)` (degree 2) → None.
        let kxx = AtomKey::from_indexed_eq(&[t(1, 2)], &[t(0, 0)], &vn, &prime);
        assert!(kxx.as_single_var_eq(&prime).is_none());
    }

    #[test]
    fn intern_eq_emits_mutex_clause_between_same_var_constants() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        let a0 = match tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let n_clauses_before = sat.n_clauses();
        let a1 = match tbl.intern_eq(&[t(1, 1)], &[t(1, 0)], &vn, &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        assert_ne!(a0, a1);
        assert!(sat.n_clauses() > n_clauses_before);
        assert!(sat.add_clause(vec![Lit::pos(a0)]));
        let added_second = sat.add_clause(vec![Lit::pos(a1)]);
        assert!(!added_second);
        assert!(sat.is_unsat());
    }

    #[test]
    fn intern_eq_no_mutex_between_same_constant_repeats() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
        let n_clauses_before = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
        assert_eq!(sat.n_clauses(), n_clauses_before);
    }

    #[test]
    fn intern_eq_no_mutex_across_different_variables() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x", "y"]);
        let ax = match tbl.intern_eq(
            &[pt(1, &[(0, 1)])],
            &[pt(0, &[])],
            &vn,
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let ay = match tbl.intern_eq(
            &[pt(1, &[(1, 1)])],
            &[pt(0, &[])],
            &vn,
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        assert!(sat.add_clause(vec![Lit::pos(ax)]));
        assert!(sat.add_clause(vec![Lit::pos(ay)]));
        assert!(!sat.is_unsat());
    }

    #[test]
    fn intern_eq_emits_three_pairwise_mutexes_for_three_constants() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        let n0 = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(0, 0)], &vn, &mut sat);
        let n1 = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(1, 0)], &vn, &mut sat);
        let n2 = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(2, 0)], &vn, &mut sat);
        let n3 = sat.n_clauses();
        assert_eq!(n1 - n0, 0);
        assert_eq!(n2 - n1, 1);
        assert_eq!(n3 - n2, 2);
    }

    #[test]
    fn mutex_invariant_under_lhs_rhs_swap() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(101u32));
        let vn = names(&["x"]);
        let r1 = tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
        let n_after_first = sat.n_clauses();
        let r2 = tbl.intern_eq(&[t(5, 0)], &[t(1, 1)], &vn, &mut sat);
        match (r1, r2) {
            (InternResult::Var(a), InternResult::Var(b)) => assert_eq!(a, b),
            _ => panic!("expected Var both times"),
        }
        assert_eq!(sat.n_clauses(), n_after_first);
    }

    #[test]
    fn single_var_eq_detects_nonunit_coefficient_via_fermat() {
        let prime = BigUint::from(7u32);
        let vn = names(&["x"]);
        let k_direct = AtomKey::from_indexed_eq(&[t(1, 1)], &[t(5, 0)], &vn, &prime);
        let (var_d, val_d) = k_direct.as_single_var_eq(&prime).expect("direct");
        assert_eq!(var_d, "x");
        assert_eq!(val_d, BigUint::from(5u32));
        let k_scaled = AtomKey::from_indexed_eq(&[t(2, 1)], &[t(3, 0)], &vn, &prime);
        let (var_s, val_s) = k_scaled.as_single_var_eq(&prime).expect("scaled");
        assert_eq!(var_s, "x");
        assert_eq!(val_s, BigUint::from(5u32));
    }

    #[test]
    fn intern_eq_emits_mutex_across_semantically_distinct_scaled_atoms() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(7u32));
        let vn = names(&["x"]);
        let n0 = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
        let n1 = sat.n_clauses();
        assert_eq!(n1 - n0, 0);
        tbl.intern_eq(&[t(2, 1)], &[t(10, 0)], &vn, &mut sat);
        let n2 = sat.n_clauses();
        assert_eq!(n2 - n1, 0);
        tbl.intern_eq(&[t(1, 1)], &[t(6, 0)], &vn, &mut sat);
        let n3 = sat.n_clauses();
        assert_eq!(n3 - n2, 2);
    }

    #[test]
    fn mutex_does_not_fire_for_equivalent_value_via_canonicalization() {
        let mut sat = Solver::new();
        let mut tbl = AtomTable::new(BigUint::from(7u32));
        let vn = names(&["x"]);
        tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
        let n_after = sat.n_clauses();
        tbl.intern_eq(&[t(1, 1)], &[t(5, 0)], &vn, &mut sat);
        assert_eq!(sat.n_clauses(), n_after);
        tbl.intern_eq(&[t(1, 1)], &[t(6, 0)], &vn, &mut sat);
        assert_eq!(sat.n_clauses(), n_after + 1);
    }
}
