//! FF theory plug-in over `core::solve_encoded_with_cancel`.
//!
//! Shape matches cvc5 `theory/ff/sub_theory.cpp`. Facts arrive via
//! [`Theory::notify_fact`] onto a level-indexed trail. Each
//! [`Theory::post_check`] at `Effort::Full` builds a
//! [`ConstraintSystem`] from the current trail, runs the GB solver,
//! and maps any `original_polys` UNSAT-core indices back to atom
//! variables.

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
    /// Per-decision-level fact trails. Each entry is `(atom_var,
    /// polarity)`. Position in the trail is the order facts arrived.
    /// `levels[k]` is the count of facts in scope at decision level
    /// `k` (so `levels[0]` is the root-level count, etc.). On `push`
    /// we snapshot the current length; on `pop` we truncate back.
    facts: Vec<(Var, bool)>,
    levels: Vec<usize>,
    /// Cached most-recent SAT model assignments (set by `post_check`
    /// when it returns `Sat`).
    last_model: Option<HashMap<String, BigUint>>,
    /// Whether the most-recent check was at full effort and produced
    /// a model. Used by `collect_model`.
    has_model: bool,
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
        }
    }

    /// Build a `ConstraintSystem` over the current trail, then encode
    /// + dispatch to the GB solver. Returns the split-GB outcome plus
    /// a mapping from `original_polys` index to atom variable so the
    /// caller can construct an atom-level UNSAT core.
    fn check_full_with_mapping(&mut self) -> CheckOutcome {
        let prime = self.atoms.prime().clone();

        // Build equalities + disequalities + assignments from the
        // current trail. Disequalities use the Rabinowitsch witness
        // scheme (a · w − 1 = 0 with w fresh per disequality), which
        // mirrors what `encoder::encode` would emit if we expressed
        // them as `disequalities` entries.
        let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
        let mut disequalities: Vec<(String, String)> = Vec::new();
        let mut assignments: Vec<(String, BigUint)> = Vec::new();
        // Atom variable that produced each pushed equality (parallel
        // to `equalities`).
        let mut equality_atoms: Vec<Var> = Vec::new();
        // Atom variable that produced each pushed disequality (parallel
        // to `disequalities`). `encoder::encode_impl` emits all
        // equalities first, THEN all Rabinowitsch polynomials in
        // disequality order, so the final encoded-input ordering is
        // `equality_atoms ++ disequality_atoms`.
        let mut disequality_atoms: Vec<Var> = Vec::new();
        let mut diseq_counter: usize = 0;
        // `__zero` is the FF zero; needed when any disequality is
        // present so `__diseq_d_i ≠ __zero` matches `d ≠ 0`.
        let mut zero_added = false;

        for &(atom_var, polarity) in &self.facts {
            let key = match self.atoms.atom(atom_var) {
                Some(k) => k,
                None => continue, // auxiliary var: no FF semantics
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
                // `encoder::encode_impl` emits inputs in the order
                // (equalities) ++ (Rabinowitsch polys). Concatenating
                // `equality_atoms` and `disequality_atoms` gives the
                // matching atom for each encoded input index.
                let mut input_atom_in_encode_order = equality_atoms;
                input_atom_in_encode_order.extend(disequality_atoms);
                let mut atom_core: Vec<Var> = core_indices
                    .iter()
                    .filter_map(|&i| input_atom_in_encode_order.get(i).copied())
                    .collect();
                atom_core.sort();
                atom_core.dedup();
                if atom_core.is_empty() {
                    // Defensive: an empty atom-core would not lead to
                    // any new learnt clause; report Unknown so the
                    // orchestrator can attempt different decisions.
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

impl<'a> Theory for FfTheory<'a> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        // Auxiliary (Tseitin) variables carry no FF semantics; only
        // SAT-level clauses constrain them.
        if self.atoms.is_auxiliary(atom) {
            return;
        }
        self.facts.push((atom, polarity));
    }

    fn post_check(&mut self, effort: Effort) -> CheckOutcome {
        if effort != Effort::Full {
            return CheckOutcome::Unknown;
        }
        self.check_full_with_mapping()
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
}
