//! FF theory plug-in over `core::solve_encoded_with_cancel`.
//!
//! Shape matches cvc5 `theory/ff/sub_theory.cpp`. Facts arrive via
//! [`Theory::notify_fact`] onto a level-indexed trail. Each
//! [`Theory::post_check`] at `Effort::Full` builds a
//! [`ConstraintSystem`] from the current trail, runs the GB solver,
//! and maps any returned UNSAT core indices back to atom variables.

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::core::{solve_encoded_with_cancel, SolveOutcome};
use crate::encoder::{encode, ConstraintSystem, PolyTerm};
use crate::sat::Var;
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::theory::{CheckOutcome, Effort, Theory};

/// FF theory plug-in: maintains an asserted-fact trail and dispatches
/// `post_check(Full)` to [`solve_encoded_with_cancel`].
pub struct FfTheory<'a> {
    atoms: &'a AtomTable,
    cancel: &'a CancelToken,
    /// `(atom_var, polarity)` in trail order. `levels[k]` snapshots
    /// `facts.len()` at the start of decision level `k+1`.
    facts: Vec<(Var, bool)>,
    levels: Vec<usize>,
    /// Most-recent SAT model from `post_check`.
    last_model: Option<HashMap<String, BigUint>>,
    has_model: bool,
    /// Reasons for the current `propagate()` round; cleared on
    /// `propagate()` entry and on `pop()`.
    pending_reasons: HashMap<Var, Vec<(Var, bool)>>,
}

impl<'a> FfTheory<'a> {
    pub fn new(atoms: &'a AtomTable, cancel: &'a CancelToken) -> Self {
        FfTheory {
            atoms,
            cancel,
            facts: Vec::new(),
            levels: Vec::new(),
            last_model: None,
            has_model: false,
            pending_reasons: HashMap::new(),
        }
    }

    /// Build a `ConstraintSystem` from the trail, encode, dispatch to
    /// the GB solver, and map any returned `original_polys` core
    /// indices back to atom variables. Encoded-input ordering is
    /// `equality_atoms ++ disequality_atoms` (see
    /// `encoder::encode_impl`).
    fn check_full_with_mapping(&mut self) -> CheckOutcome {
        let prime = self.atoms.prime().clone();

        let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
        let mut disequalities: Vec<(String, String)> = Vec::new();
        let mut assignments: Vec<(String, BigUint)> = Vec::new();
        let mut equality_atoms: Vec<Var> = Vec::new();
        let mut disequality_atoms: Vec<Var> = Vec::new();
        let mut diseq_counter: usize = 0;
        let mut zero_added = false;

        for &(atom_var, polarity) in &self.facts {
            let key = match self.atoms.atom(atom_var) {
                Some(k) => k,
                None => continue,
            };
            if polarity {
                equalities.push(key.to_poly_terms());
                equality_atoms.push(atom_var);
            } else {
                let d_name = format!("__diseq_d_{}", diseq_counter);
                diseq_counter += 1;
                let mut def: Vec<PolyTerm> = vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![d_name.clone()],
                }];
                for t in key.terms.iter() {
                    let neg_coeff = if t.0.is_zero() {
                        BigUint::zero()
                    } else {
                        &prime - &t.0
                    };
                    def.push(PolyTerm {
                        coeff: neg_coeff,
                        vars: t.1.clone(),
                    });
                }
                equalities.push(def);
                equality_atoms.push(atom_var);
                disequalities.push((d_name, "__zero".to_string()));
                disequality_atoms.push(atom_var);
                if !zero_added {
                    assignments.push(("__zero".into(), BigUint::zero()));
                    zero_added = true;
                }
            }
        }

        if equalities.is_empty() && disequalities.is_empty() {
            self.last_model = Some(HashMap::new());
            self.has_model = true;
            return CheckOutcome::Sat;
        }

        let sys = ConstraintSystem {
            prime,
            equalities,
            disequalities,
            assignments,
            add_field_polys: false,
            bitsums: vec![],
        };
        let encoded = match encode(&sys) {
            Ok(e) => e,
            Err(_) => return CheckOutcome::Unknown,
        };

        if self.cancel.is_cancelled() {
            return CheckOutcome::Unknown;
        }

        match solve_encoded_with_cancel(&encoded, self.cancel) {
            SolveOutcome::Sat(model) => {
                self.last_model = Some(model);
                self.has_model = true;
                CheckOutcome::Sat
            }
            SolveOutcome::Unsat(core_indices) => {
                self.has_model = false;
                let mut input_atom_in_encode_order = equality_atoms;
                input_atom_in_encode_order.extend(disequality_atoms);
                let mut atom_core: Vec<Var> = core_indices
                    .iter()
                    .filter_map(|&i| input_atom_in_encode_order.get(i).copied())
                    .collect();
                atom_core.sort();
                atom_core.dedup();
                if atom_core.is_empty() {
                    return CheckOutcome::Unknown;
                }
                CheckOutcome::Unsat { core: atom_core }
            }
            SolveOutcome::Unknown => {
                self.has_model = false;
                CheckOutcome::Unknown
            }
        }
    }
}

impl<'a> FfTheory<'a> {
    /// `var_name -> (value, source_atom)` from positive single-variable
    /// equalities on the trail.
    fn pinned_vars(&self) -> HashMap<String, (BigUint, Var)> {
        let prime = self.atoms.prime();
        let mut pinned: HashMap<String, (BigUint, Var)> = HashMap::new();
        for &(av, pol) in &self.facts {
            if !pol {
                continue;
            }
            let key = match self.atoms.atom(av) {
                Some(k) => k,
                None => continue,
            };
            if let Some((var, value)) = key.as_single_var_eq(prime) {
                pinned.insert(var, (value, av));
            }
        }
        pinned
    }

    /// Evaluate `key` under `pinned`. `None` when any variable is unpinned.
    fn eval_key(
        &self,
        key: &super::atoms::AtomKey,
        pinned: &HashMap<String, (BigUint, Var)>,
    ) -> Option<BigUint> {
        let prime = self.atoms.prime();
        let mut acc = BigUint::zero();
        for (coeff, vars) in &key.terms {
            let mut term_value = coeff.clone();
            for var in vars {
                let (v, _) = pinned.get(var)?;
                term_value = (term_value * v) % prime;
            }
            acc = (acc + term_value) % prime;
        }
        Some(acc)
    }

    /// Tier 1: atom polynomial fully reduces under `pinned`; derive its
    /// truth from the constant result. Reason = pinning sources.
    fn compute_tier1(
        &self,
        pinned: &HashMap<String, (BigUint, Var)>,
    ) -> Vec<(Var, bool, Vec<(Var, bool)>)> {
        if pinned.is_empty() {
            return Vec::new();
        }
        let on_trail: std::collections::HashSet<Var> =
            self.facts.iter().map(|&(av, _)| av).collect();
        let mut results = Vec::new();
        for i in 0..self.atoms.n_atom_slots() {
            let v = Var(i as u32);
            if on_trail.contains(&v) {
                continue;
            }
            let key = match self.atoms.atom(v) {
                Some(k) => k,
                None => continue,
            };
            let acc = match self.eval_key(key, pinned) {
                Some(val) => val,
                None => continue,
            };
            let used_vars: std::collections::HashSet<&String> = key
                .terms
                .iter()
                .flat_map(|(_, vs)| vs.iter())
                .collect();
            // Constant-only atom: skip to avoid an empty-reason
            // propagation (handled at root by `post_check`).
            if used_vars.is_empty() {
                continue;
            }
            let mut reason: Vec<(Var, bool)> = Vec::new();
            let mut included: std::collections::HashSet<Var> = std::collections::HashSet::new();
            for var in &used_vars {
                if let Some((_, src)) = pinned.get(*var) {
                    if included.insert(*src) {
                        reason.push((*src, true));
                    }
                }
            }
            results.push((v, acc.is_zero(), reason));
        }
        results
    }

    /// Tier 2: a positive multi-var atom A on the trail reduces under
    /// `pinned` to `a·v + c = 0` (single unpinned linear var `v`, `a ≠ 0`).
    /// Solve `v = −c · a⁻¹ mod p` (Fermat); for each `(= v c')` in the
    /// table, propagate True iff `c' = derived_value` else False.
    /// Reason = `[A] + pinning sources for the other vars in A`.
    fn compute_tier2(
        &self,
        pinned: &HashMap<String, (BigUint, Var)>,
    ) -> Vec<(Var, bool, Vec<(Var, bool)>)> {
        let prime = self.atoms.prime();
        let on_trail: std::collections::HashSet<Var> =
            self.facts.iter().map(|&(av, _)| av).collect();
        let one = BigUint::from(1u32);
        let two = BigUint::from(2u32);
        let mut results = Vec::new();
        for &(src_av, src_pol) in &self.facts {
            if !src_pol {
                continue;
            }
            let src_key = match self.atoms.atom(src_av) {
                Some(k) => k,
                None => continue,
            };
            if src_key.as_single_var_eq(prime).is_some() {
                continue;
            }
            let mut acc_const = BigUint::zero();
            let mut unpinned: Option<String> = None;
            let mut unpinned_coeff = BigUint::zero();
            let mut other_used_sources: Vec<Var> = Vec::new();
            let mut already_included: std::collections::HashSet<Var> =
                std::collections::HashSet::new();
            let mut bad = false;
            for (coeff, vars) in &src_key.terms {
                let mut pinned_product = one.clone();
                let mut term_unpinned: Option<String> = None;
                let mut term_unpinned_count: usize = 0;
                for var in vars {
                    match pinned.get(var) {
                        Some((val, src)) => {
                            pinned_product = (pinned_product * val) % prime;
                            if already_included.insert(*src) {
                                other_used_sources.push(*src);
                            }
                        }
                        None => {
                            term_unpinned_count += 1;
                            term_unpinned = Some(var.clone());
                        }
                    }
                }
                if term_unpinned_count == 0 {
                    let term_val = (coeff * &pinned_product) % prime;
                    acc_const = (acc_const + term_val) % prime;
                } else if term_unpinned_count == 1 {
                    let var = term_unpinned.expect("set when count == 1");
                    match &unpinned {
                        None => unpinned = Some(var),
                        Some(prev) if prev == &var => {}
                        _ => {
                            bad = true;
                            break;
                        }
                    }
                    let term_val = (coeff * &pinned_product) % prime;
                    unpinned_coeff = (unpinned_coeff + term_val) % prime;
                } else {
                    bad = true;
                    break;
                }
            }
            if bad {
                continue;
            }
            let var_name = match unpinned {
                Some(v) => v,
                None => continue,
            };
            if unpinned_coeff.is_zero() {
                continue;
            }
            let neg_c = if acc_const.is_zero() {
                BigUint::zero()
            } else {
                prime - &acc_const
            };
            let inv_a = if unpinned_coeff == one {
                one.clone()
            } else {
                if prime <= &two {
                    continue;
                }
                unpinned_coeff.modpow(&(prime - &two), prime)
            };
            let derived_value = (neg_c * inv_a) % prime;
            let mut reason_base: Vec<(Var, bool)> =
                Vec::with_capacity(other_used_sources.len() + 1);
            reason_base.push((src_av, true));
            for src in &other_used_sources {
                reason_base.push((*src, true));
            }
            for (other_value, other_atom_var) in self.atoms.atoms_for_var(&var_name) {
                if *other_atom_var == src_av {
                    continue;
                }
                if on_trail.contains(other_atom_var) {
                    continue;
                }
                let polarity = other_value == &derived_value;
                results.push((*other_atom_var, polarity, reason_base.clone()));
            }
        }
        results
    }
}

impl<'a> Theory for FfTheory<'a> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        if self.atoms.is_auxiliary(atom) {
            return;
        }
        self.facts.push((atom, polarity));
    }

    fn push(&mut self) {
        self.levels.push(self.facts.len());
    }

    fn pop(&mut self) {
        if let Some(saved_len) = self.levels.pop() {
            self.facts.truncate(saved_len);
        }
        self.has_model = false;
        self.last_model = None;
        self.pending_reasons.clear();
    }

    fn post_check(&mut self, effort: Effort) -> CheckOutcome {
        if effort != Effort::Full {
            return CheckOutcome::Unknown;
        }
        self.check_full_with_mapping()
    }

    /// Two-tier propagation; reasons cached in `pending_reasons` for
    /// `explain()`. See [`compute_tier1`] and [`compute_tier2`].
    fn propagate(&mut self) -> Vec<(Var, bool)> {
        self.pending_reasons.clear();
        let pinned = self.pinned_vars();
        let tier1 = self.compute_tier1(&pinned);
        let tier2 = self.compute_tier2(&pinned);
        let mut props: Vec<(Var, bool)> = Vec::new();
        let mut seen: std::collections::HashSet<Var> = std::collections::HashSet::new();
        for (atom_v, polarity, reason) in tier1.into_iter().chain(tier2.into_iter()) {
            if seen.insert(atom_v) {
                props.push((atom_v, polarity));
                self.pending_reasons.insert(atom_v, reason);
            }
        }
        props
    }

    /// Cached reason for an atom returned by the most recent
    /// `propagate()`. Empty result on cache miss is treated as a
    /// contract violation by `enqueue_theory`.
    fn explain(&self, atom: Var, _polarity: bool) -> Vec<(Var, bool)> {
        self.pending_reasons
            .get(&atom)
            .cloned()
            .unwrap_or_default()
    }

    fn level(&self) -> u32 {
        self.levels.len() as u32
    }

    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        if self.has_model {
            self.last_model.clone()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cdclt::atoms::{AtomTable, InternResult};
    use crate::encoder::PolyTerm;
    use crate::sat::Solver;
    use num_bigint::BigUint;

    fn t(coeff: u64, vars: &[&str]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// Atom variable for `(= var const)` over the given table + SAT.
    fn intern_eq_var(
        tbl: &mut AtomTable,
        sat: &mut Solver,
        var: &str,
        c: u64,
    ) -> Var {
        let r = tbl.intern_eq(&[t(1, &[var])], &[t(c, &[])], sat);
        match r {
            InternResult::Var(v) => v,
            _ => panic!("expected Var"),
        }
    }

    #[test]
    fn empty_trail_is_sat() {
        let prime = BigUint::from(101u32);
        let atoms = AtomTable::new(prime);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        match th.post_check(Effort::Full) {
            CheckOutcome::Sat => {}
            other => panic!("expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn single_eq_sat() {
        // (= x 5): SAT, model x=5.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let av = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(av, true);
        match th.post_check(Effort::Full) {
            CheckOutcome::Sat => {}
            other => panic!("expected Sat, got {:?}", other),
        }
        let m = th.collect_model().expect("model present");
        assert_eq!(m.get("x"), Some(&BigUint::from(5u32)));
    }

    #[test]
    fn two_contradictory_eqs_unsat() {
        // (= x 5) ∧ (= x 6): UNSAT, core includes both atoms.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let a1 = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let a2 = intern_eq_var(&mut atoms, &mut sat, "x", 6);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(a1, true);
        th.notify_fact(a2, true);
        match th.post_check(Effort::Full) {
            CheckOutcome::Unsat { core } => {
                assert!(core.contains(&a1));
                assert!(core.contains(&a2));
            }
            other => panic!("expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn neq_via_negative_polarity() {
        // (= x 5) ∧ (¬(= x 5)): the same atom asserted with both
        // polarities — SAT layer would catch this, but the theory
        // also handles it via the Rabinowitsch encoding.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let av = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(av, true);
        th.notify_fact(av, false);
        match th.post_check(Effort::Full) {
            CheckOutcome::Unsat { core } => {
                assert!(core.contains(&av));
            }
            other => panic!("expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn push_pop_undoes_facts() {
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let av = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.push();
        th.notify_fact(av, true);
        assert_eq!(th.facts.len(), 1);
        th.pop();
        assert_eq!(th.facts.len(), 0);
    }

    #[test]
    fn propagate_empty_when_no_pinned_vars() {
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let _ = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        // Without any True fact, no var is pinned ⇒ no propagation.
        assert!(th.propagate().is_empty());
    }

    #[test]
    fn propagate_pins_force_other_atom_truth() {
        // Two atoms over the same variable: (= x 5) and (= x 6).
        // Asserting (= x 5) True pins x = 5; propagation then derives
        // (= x 6) is False.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let a5 = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let a6 = intern_eq_var(&mut atoms, &mut sat, "x", 6);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(a5, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == a6 && !p),
            "expected (a6, false) in propagations: {:?}",
            props
        );
    }

    #[test]
    fn propagate_pins_force_multi_var_atom_true() {
        // (= (ff.add x y) 7) with x=3, y=4 evaluates to 0 ⇒ atom True.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let ay = intern_eq_var(&mut atoms, &mut sat, "y", 4);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax, true);
        th.notify_fact(ay, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == asum && p),
            "expected (asum, true): {:?}",
            props
        );
    }

    #[test]
    fn explain_returns_only_relevant_pinning_facts() {
        // Pin x=3 and y=4; the propagated atom (x+y=7) depends on both,
        // so explain must return both. A third pinned variable z that
        // doesn't appear in the atom must NOT show up.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let ay = intern_eq_var(&mut atoms, &mut sat, "y", 4);
        let az = intern_eq_var(&mut atoms, &mut sat, "z", 9);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax, true);
        th.notify_fact(ay, true);
        th.notify_fact(az, true);
        let _ = th.propagate(); // populate pending_reasons
        let reason = th.explain(asum, true);
        let reason_vars: std::collections::HashSet<Var> =
            reason.iter().map(|&(v, _)| v).collect();
        assert!(reason_vars.contains(&ax));
        assert!(reason_vars.contains(&ay));
        assert!(!reason_vars.contains(&az), "z should not appear in reason");
    }

    #[test]
    fn propagate_ignores_negative_polarity_facts() {
        // (≠) facts must not contribute to pinning.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let a5 = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let _a6 = intern_eq_var(&mut atoms, &mut sat, "x", 6);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(a5, false);
        assert!(
            th.propagate().is_empty(),
            "negative-polarity (x ≠ 5) must not pin x to 5"
        );
    }

    #[test]
    fn propagate_ignores_auxiliary_variables() {
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let _a5 = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let aux = atoms.new_aux(&mut sat);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(aux, true);
        assert_eq!(th.facts.len(), 0, "aux var must not be recorded");
        assert!(th.propagate().is_empty());
    }

    #[test]
    fn propagate_handles_degree_two_atom_when_var_pinned() {
        // x=2 + (x*x = 4) atom ⇒ True under substitution.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax2 = intern_eq_var(&mut atoms, &mut sat, "x", 2);
        let asq = match atoms.intern_eq(&[t(1, &["x", "x"])], &[t(4, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax2, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == asq && p),
            "(x*x = 4) under x=2 must propagate True: {:?}",
            props
        );
    }

    #[test]
    fn propagate_skips_atom_with_unpinned_variable() {
        // Tier 1 requires all vars pinned; partial pinning must skip.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        let props = th.propagate();
        assert!(
            !props.iter().any(|&(v, _)| v == asum),
            "(x+y=7) must not propagate while y is unpinned: {:?}",
            props
        );
    }

    #[test]
    fn pinning_is_idempotent_across_canonically_distinct_but_equivalent_atoms() {
        // (= x 5) and (2x = 10) both pin x=5 via Fermat.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let a_x5 = intern_eq_var(&mut atoms, &mut sat, "x", 5);
        let a_2x10 = match atoms.intern_eq(&[t(2, &["x"])], &[t(10, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let a_x6 = intern_eq_var(&mut atoms, &mut sat, "x", 6);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(a_x5, true);
        th.notify_fact(a_2x10, true);
        let pinned = th.pinned_vars();
        let (value, _src) = pinned.get("x").expect("x must be pinned");
        assert_eq!(value, &BigUint::from(5u32));
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == a_x6 && !p),
            "x=5 (asserted twice canonically distinct) must still derive x≠6: {:?}",
            props
        );
    }

    #[test]
    fn propagate_handles_constant_only_atoms_without_panic() {
        // (= 0 1) interns as a vars-empty atom; propagate must not panic.
        let prime = BigUint::from(7u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let av = match atoms.intern_eq(&[t(0, &[])], &[t(1, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!("(= 0 1) interns to a real atom on GF(7)"),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(av, true);
        let _ = th.propagate(); // must not panic
    }

    #[test]
    fn tier2_linear_residue_derives_target_atom_true() {
        // x=3 + (x+y=7) ⇒ y=4 ⇒ (= y 4) True.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let ay4 = intern_eq_var(&mut atoms, &mut sat, "y", 4);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        th.notify_fact(asum, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == ay4 && p),
            "Tier 2 must derive (= y 4) True from (= x 3) and (= (x+y) 7): {:?}",
            props
        );
    }

    #[test]
    fn tier2_propagates_false_for_non_matching_value_atom() {
        // Derived y=4 ⇒ (= y 5) False.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let _ay4 = intern_eq_var(&mut atoms, &mut sat, "y", 4);
        let ay5 = intern_eq_var(&mut atoms, &mut sat, "y", 5);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        th.notify_fact(asum, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == ay5 && !p),
            "Tier 2 must derive (= y 5) False (derived value is 4): {:?}",
            props
        );
    }

    #[test]
    fn tier2_skips_multiple_unpinned_variables() {
        // (x+y+z=10) with only x pinned: 2 unpinned vars ⇒ Tier 2 bails.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let _ay7 = intern_eq_var(&mut atoms, &mut sat, "y", 7);
        let _az0 = intern_eq_var(&mut atoms, &mut sat, "z", 0);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"]), t(1, &["z"])],
            &[t(10, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        th.notify_fact(asum, true);
        let props = th.propagate();
        for (av, _) in &props {
            assert_ne!(*av, _ay7);
            assert_ne!(*av, _az0);
        }
    }

    #[test]
    fn tier2_skips_degree_two_in_unpinned() {
        // (y*z = 12) has a bivariate unpinned term ⇒ Tier 2 bails.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let _ay3 = intern_eq_var(&mut atoms, &mut sat, "y", 3);
        let aprod = match atoms.intern_eq(&[t(1, &["y", "z"])], &[t(12, &[])], &mut sat) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        th.notify_fact(aprod, true);
        let props = th.propagate();
        assert!(!props.iter().any(|&(v, _)| v == aprod));
    }

    #[test]
    fn tier2_explain_includes_source_atom_and_other_pinning_facts() {
        // Reason for (= y 4) True = {source (x+y=7), pinning (= x 3)}.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let ay4 = intern_eq_var(&mut atoms, &mut sat, "y", 4);
        let asum = match atoms.intern_eq(
            &[t(1, &["x"]), t(1, &["y"])],
            &[t(7, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax3, true);
        th.notify_fact(asum, true);
        let _ = th.propagate();
        let reason = th.explain(ay4, true);
        let reason_vars: std::collections::HashSet<Var> =
            reason.iter().map(|&(v, _)| v).collect();
        assert!(
            reason_vars.contains(&asum),
            "Tier 2 reason must cite the source atom: {:?}",
            reason
        );
        assert!(
            reason_vars.contains(&ax3),
            "Tier 2 reason must cite the pinning fact: {:?}",
            reason
        );
    }

    #[test]
    fn tier2_nonlinear_coefficient_from_pinned_factor() {
        // (x*y = 12) with x=4 pinned: 4y=12 ⇒ y=3.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let ax4 = intern_eq_var(&mut atoms, &mut sat, "x", 4);
        let ay3 = intern_eq_var(&mut atoms, &mut sat, "y", 3);
        let aprod = match atoms.intern_eq(
            &[t(1, &["x", "y"])],
            &[t(12, &[])],
            &mut sat,
        ) {
            InternResult::Var(v) => v,
            _ => panic!(),
        };
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.notify_fact(ax4, true);
        th.notify_fact(aprod, true);
        let props = th.propagate();
        assert!(
            props.iter().any(|&(v, p)| v == ay3 && p),
            "Tier 2 with non-unit pinned-factor coefficient must solve 4y=12 ⇒ y=3: {:?}",
            props
        );
    }

    #[test]
    fn pop_clears_pinning_so_propagate_returns_empty() {
        // pop() drops facts, so the (= x 6) propagation no longer fires.
        let prime = BigUint::from(101u32);
        let mut atoms = AtomTable::new(prime);
        let mut sat = Solver::new();
        let a3 = intern_eq_var(&mut atoms, &mut sat, "x", 3);
        let _a6 = intern_eq_var(&mut atoms, &mut sat, "x", 6);
        let cancel = CancelToken::none();
        let mut th = FfTheory::new(&atoms, &cancel);
        th.push();
        th.notify_fact(a3, true);
        assert!(!th.propagate().is_empty());
        th.pop();
        assert!(th.propagate().is_empty());
    }
}
