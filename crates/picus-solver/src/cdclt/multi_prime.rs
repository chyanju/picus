//! Multi-prime FF theory router.
//!
//! Wraps one [`AtomTable`] per distinct GF(p) appearing in input and
//! routes [`Theory::notify_fact`] / [`Theory::post_check`] to the per-prime
//! [`check_full_with_atoms`] slot. Matches cvc5's `unordered_map<TypeNode,
//! SubTheory>` shape in `theory_ff.cpp`.
//!
//! The router is additive — it does not replace [`super::ff_theory::FfTheory`]
//! on the single-prime path. The orchestrator constructs the single-prime
//! `FfTheory` directly; the router is exposed for callers (future SMT-LIB
//! frontend with mixed-prime inputs) that need per-prime partitioning.

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::sat::Var;
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::ff_theory::check_full_with_atoms;
use super::theory::{CheckOutcome, Theory};

/// Per-prime slot in the router. Owns the prime's atom table and trail.
pub struct PrimeSlot {
    pub atoms: AtomTable,
    facts: Vec<(Var, bool)>,
    levels: Vec<usize>,
    last_model: Option<HashMap<String, BigUint>>,
    has_model: bool,
}

/// Multi-prime FF theory router. One [`PrimeSlot`] per distinct GF(p).
pub struct FfTheoryRouter<'a> {
    slots: Vec<PrimeSlot>,
    prime_to_idx: HashMap<BigUint, usize>,
    /// Atom variable → slot index (the prime its atom belongs to).
    /// Populated by the caller via [`FfTheoryRouter::assign_var`].
    var_to_slot: HashMap<Var, usize>,
    cancel: &'a CancelToken,
}

impl<'a> FfTheoryRouter<'a> {
    /// Construct a router from a list of per-prime atom tables. Each
    /// table must use a distinct prime; later duplicates overwrite the
    /// `prime → idx` mapping but the slot itself stays separate.
    pub fn new(atoms_by_prime: Vec<AtomTable>, cancel: &'a CancelToken) -> Self {
        let mut prime_to_idx = HashMap::new();
        let mut slots = Vec::with_capacity(atoms_by_prime.len());
        for (i, at) in atoms_by_prime.into_iter().enumerate() {
            prime_to_idx.insert(at.prime().clone(), i);
            slots.push(PrimeSlot {
                atoms: at,
                facts: Vec::new(),
                levels: Vec::new(),
                last_model: None,
                has_model: false,
            });
        }
        FfTheoryRouter {
            slots,
            prime_to_idx,
            var_to_slot: HashMap::new(),
            cancel,
        }
    }

    pub fn n_primes(&self) -> usize {
        self.slots.len()
    }

    /// Return the slot index for a given prime, or `None` if not registered.
    pub fn slot_idx_for(&self, prime: &BigUint) -> Option<usize> {
        self.prime_to_idx.get(prime).copied()
    }

    /// Mutable borrow of a slot's atom table for atom interning by the caller.
    pub fn slot_atoms_mut(&mut self, slot_idx: usize) -> &mut AtomTable {
        &mut self.slots[slot_idx].atoms
    }

    /// Register that the SAT variable `var` belongs to the prime at `slot_idx`.
    /// Calls without registration are silently dropped (fact never reaches
    /// any sub-theory) — the caller is responsible for registering every
    /// atom variable that may arrive through [`Theory::notify_fact`].
    pub fn assign_var(&mut self, var: Var, slot_idx: usize) {
        self.var_to_slot.insert(var, slot_idx);
    }
}

impl<'a> Theory for FfTheoryRouter<'a> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        if let Some(&idx) = self.var_to_slot.get(&atom) {
            self.slots[idx].facts.push((atom, polarity));
        }
    }

    /// Run each slot's FF check independently and combine: any UNSAT
    /// short-circuits to UNSAT (with concatenated core from every UNSAT
    /// slot); else if any UNKNOWN → UNKNOWN; else SAT. The combined core
    /// concatenates per-prime cores so the orchestrator learns the union.
    fn post_check(&mut self) -> CheckOutcome {
        let mut combined_core: Vec<Var> = Vec::new();
        let mut any_unknown = false;
        for slot in &mut self.slots {
            let (outcome, model) = check_full_with_atoms(&slot.atoms, &slot.facts, self.cancel);
            match outcome {
                CheckOutcome::Sat => {
                    slot.last_model = model;
                    slot.has_model = true;
                }
                CheckOutcome::Unsat { core } => {
                    slot.has_model = false;
                    combined_core.extend(core);
                }
                CheckOutcome::Unknown => {
                    slot.has_model = false;
                    any_unknown = true;
                }
            }
        }
        if !combined_core.is_empty() {
            CheckOutcome::Unsat {
                core: combined_core,
            }
        } else if any_unknown {
            CheckOutcome::Unknown
        } else {
            CheckOutcome::Sat
        }
    }

    fn push(&mut self) {
        for slot in &mut self.slots {
            slot.levels.push(slot.facts.len());
        }
    }

    fn pop(&mut self) {
        for slot in &mut self.slots {
            if let Some(h) = slot.levels.pop() {
                slot.facts.truncate(h);
            }
            slot.has_model = false;
        }
    }

    /// Union the per-prime models. Returns `None` unless every slot has a
    /// model; the orchestrator should only call this after a SAT outcome.
    /// Variable names are assumed distinct across primes (the caller is
    /// responsible for namespacing); equal-name collisions take the last
    /// slot's value.
    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        let mut merged: HashMap<String, BigUint> = HashMap::new();
        for slot in &self.slots {
            if !slot.has_model {
                return None;
            }
            if let Some(m) = &slot.last_model {
                for (k, v) in m {
                    merged.insert(k.clone(), v.clone());
                }
            }
        }
        Some(merged)
    }
}

#[cfg(test)]
#[path = "multi_prime_tests.rs"]
mod tests;
