//! Cross-decision incremental FF theory state.
//!
//! Parallel [`Theory`] implementation to [`super::ff_theory::FfTheory`].
//! Each [`notify_fact`] translates the asserted atom into a [`DensePoly`]
//! on a pre-allocated ring and pushes it into an [`IncrementalGB`];
//! [`push`] / [`pop`] forward to the engine's checkpointing so the
//! Groebner basis is amortized across SAT decisions instead of rebuilt
//! per check. Mirrors cvc5's `CDList<Node>` + persistent GBasis layout.

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;

use picus_core::ff::field::PrimeField;
use picus_core::ff::monomial::{Monomial, MonomialOrder};
use picus_core::ff::polynomial::{DensePoly, PolyRing};

use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
use crate::sat::Var;
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::theory::{CheckOutcome, Theory};

/// Cross-decision incremental FF theory state.
///
/// Construct with a maximum-variable budget (slots are pre-allocated in
/// the ring). New atom variable names claim slots lazily; the budget caps
/// the maximum distinct (user + witness) variables. Disequalities use the
/// Rabinowitsch trick `(lhs)*w − 1 = 0` with one fresh witness slot per
/// disequality.
pub struct IncrementalFfTheoryState<'a> {
    atoms: &'a AtomTable,
    cancel: &'a CancelToken,
    field: PrimeField,
    ring: Arc<PolyRing>,
    igb: IncrementalGB,
    /// Whether to inject the field polynomial `x^p − x = 0` for each
    /// claimed slot (true iff prime ≤ 1000).
    add_field_polys: bool,
    /// Variable name → ring slot index. Grows monotonically.
    name_to_slot: HashMap<String, usize>,
    next_slot: usize,
    /// Maximum slots allowed (the ring's variable count).
    max_slots: usize,
    /// SAT-trail of asserted facts.
    facts: Vec<(Var, bool)>,
    /// Per-level snapshot of state whose rollback must be atomic with
    /// the [`IncrementalGB`] basis. `name_to_slot` / `next_slot` are
    /// captured because [`get_or_create_slot`] injects `x^p − x` into the
    /// basis at the level the slot is claimed; without the snapshot, a
    /// `pop` rolls back the basis but leaves the slot claimed, so the
    /// next reuse short-circuits and the field polynomial is never
    /// re-injected (UNSAT then read as Sat under the `add_field_polys`
    /// branch).
    levels: Vec<LevelCheckpoint>,
    /// Per-disequality counter for witness slot naming.
    diseq_counter: usize,
    /// Cached last SAT model.
    last_model: Option<HashMap<String, BigUint>>,
    has_model: bool,
    /// Sticky flag set whenever [`build_atom_polys`] cannot encode a
    /// fact (slot budget exhausted, or atom not registered). While set,
    /// [`post_check`] returns [`CheckOutcome::Unknown`] unconditionally:
    /// the trail no longer matches the algebraic state in `igb`, so no
    /// SAT/UNSAT verdict is safe. Snapshotted in `levels` so a `pop`
    /// past the degradation point clears it.
    degraded: bool,
}

struct LevelCheckpoint {
    facts_len: usize,
    name_to_slot: HashMap<String, usize>,
    next_slot: usize,
    diseq_counter: usize,
    degraded: bool,
}

impl<'a> IncrementalFfTheoryState<'a> {
    pub fn new(atoms: &'a AtomTable, cancel: &'a CancelToken, max_vars: usize) -> Self {
        let prime = atoms.prime().clone();
        let field = PrimeField::new(prime.clone());
        let names: Vec<String> = (0..max_vars).map(|i| format!("__slot_{}", i)).collect();
        let ring = PolyRing::new(field.clone(), names, MonomialOrder::DegRevLex);
        let igb = IncrementalGB::new(ring.clone(), BuchbergerConfig::default());
        let add_field_polys = prime <= BigUint::from(1000u32);
        Self {
            atoms,
            cancel,
            field,
            ring,
            igb,
            add_field_polys,
            name_to_slot: HashMap::new(),
            next_slot: 0,
            max_slots: max_vars,
            facts: Vec::new(),
            levels: Vec::new(),
            diseq_counter: 0,
            last_model: None,
            has_model: false,
            degraded: false,
        }
    }

    /// Returns the ring slot for `name`, claiming a new slot if it is the
    /// first appearance. If `add_field_polys` is set, pushes the field
    /// polynomial `x^p − x` for the new slot into the basis.
    fn get_or_create_slot(&mut self, name: &str) -> Option<usize> {
        if let Some(&s) = self.name_to_slot.get(name) {
            return Some(s);
        }
        if self.next_slot >= self.max_slots {
            return None;
        }
        let slot = self.next_slot;
        self.name_to_slot.insert(name.to_string(), slot);
        self.next_slot += 1;
        if self.add_field_polys {
            if let Some(fp) = self.field_poly_for_slot(slot) {
                let _ = self.igb.add_generators(vec![fp]);
            }
        }
        Some(slot)
    }

    /// `x_slot^p − x_slot` as a dense poly. Exponent vectors are padded
    /// to `self.max_slots` so they line up with the ring's variable count.
    fn field_poly_for_slot(&self, slot: usize) -> Option<DensePoly> {
        let prime = self.atoms.prime();
        let p_usize = prime.to_string().parse::<u32>().ok()?;
        let m_xp_exps: Vec<u16> = (0..self.max_slots)
            .map(|i| if i == slot { p_usize as u16 } else { 0 })
            .collect();
        let m_x_exps: Vec<u16> = (0..self.max_slots)
            .map(|i| if i == slot { 1 } else { 0 })
            .collect();
        let m_xp = Monomial::from_exponents(m_xp_exps);
        let m_x = Monomial::from_exponents(m_x_exps);
        let one = self.field.one();
        let neg_one = self.field.neg(&one);
        let terms = vec![(m_xp, one), (m_x, neg_one)];
        Some(DensePoly::from_terms(terms, &self.ring))
    }

    /// Build a dense poly for the atom `atom_var` and polarity.
    /// Positive: `sum(coeff · prod_vars) = 0` → return the LHS as one poly.
    /// Negative: Rabinowitsch trick `(LHS) · w − 1 = 0` with a fresh
    /// witness slot named `__w_diseq_<n>`.
    fn build_atom_polys(&mut self, atom_var: Var, polarity: bool) -> Option<Vec<DensePoly>> {
        let key = self.atoms.atom(atom_var)?;
        let mut acc = DensePoly::zero();
        for (coeff, var_names) in &key.terms {
            let c = self.field.from_biguint(coeff);
            let mut m_exps: Vec<u16> = vec![0; self.max_slots];
            for name in var_names {
                let slot = self.get_or_create_slot(name)?;
                m_exps[slot] += 1;
            }
            let mono = Monomial::from_exponents(m_exps);
            let term_poly = DensePoly::from_terms(vec![(mono, c)], &self.ring);
            acc = acc.add(&term_poly, &self.ring);
        }
        if polarity {
            return Some(vec![acc]);
        }
        let witness_name = format!("__w_diseq_{}", self.diseq_counter);
        self.diseq_counter += 1;
        let w_slot = self.get_or_create_slot(&witness_name)?;
        let w_exps: Vec<u16> = (0..self.max_slots)
            .map(|i| if i == w_slot { 1 } else { 0 })
            .collect();
        let w_mono = Monomial::from_exponents(w_exps);
        let w_poly = DensePoly::from_terms(vec![(w_mono, self.field.one())], &self.ring);
        let product = acc.mul(&w_poly, &self.ring);
        let one_poly = DensePoly::from_terms(
            vec![(Monomial::from_exponents(vec![0; self.max_slots]), self.field.one())],
            &self.ring,
        );
        let rabinowitsch = product.sub(&one_poly, &self.ring);
        Some(vec![rabinowitsch])
    }
}

impl<'a> Theory for IncrementalFfTheoryState<'a> {
    fn notify_fact(&mut self, atom: Var, polarity: bool) {
        // Compute polys before mutating the trail: if `build_atom_polys`
        // returns `None` (unregistered atom or slot budget exhausted) the
        // fact cannot be reflected in `igb`, and pushing it onto `facts`
        // anyway would desynchronize the trail from the algebraic state.
        // The `degraded` flag forces `post_check` to Unknown until a
        // `pop` undoes the offending level.
        let polys = match self.build_atom_polys(atom, polarity) {
            Some(p) => p,
            None => {
                self.degraded = true;
                return;
            }
        };
        self.facts.push((atom, polarity));
        let _ = self.igb.add_generators(polys);
    }

    fn post_check(&mut self) -> CheckOutcome {
        if self.cancel.is_cancelled() {
            return CheckOutcome::Unknown;
        }
        if self.degraded {
            self.has_model = false;
            return CheckOutcome::Unknown;
        }
        if self.facts.is_empty() {
            self.has_model = true;
            self.last_model = Some(HashMap::new());
            return CheckOutcome::Sat;
        }
        if self.igb.is_trivial() {
            self.has_model = false;
            return CheckOutcome::Unsat {
                core: self.facts.iter().map(|(v, _)| *v).collect(),
            };
        }
        // Basis is non-trivial — the trail is satisfiable as a polynomial
        // system over the algebraic closure. For QF_FF over GF(p), the
        // caller must also verify a SAT model lies in GF(p); for small
        // primes the field polynomials we injected ensure this. Returning
        // SAT here is sound when the basis is non-trivial AND field polys
        // are present (small prime); for large primes (BN254) the basis
        // alone does not certify GF(p)-SAT, so the result is Unknown until
        // model extraction confirms.
        if self.add_field_polys {
            self.has_model = false; // model extraction deferred
            self.last_model = Some(HashMap::new());
            CheckOutcome::Sat
        } else {
            CheckOutcome::Unknown
        }
    }

    fn push(&mut self) {
        self.levels.push(LevelCheckpoint {
            facts_len: self.facts.len(),
            name_to_slot: self.name_to_slot.clone(),
            next_slot: self.next_slot,
            diseq_counter: self.diseq_counter,
            degraded: self.degraded,
        });
        self.igb.push();
    }

    fn pop(&mut self) {
        if let Some(cp) = self.levels.pop() {
            self.facts.truncate(cp.facts_len);
            self.name_to_slot = cp.name_to_slot;
            self.next_slot = cp.next_slot;
            self.diseq_counter = cp.diseq_counter;
            self.degraded = cp.degraded;
        }
        self.igb.pop();
        self.has_model = false;
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
#[path = "ff_theory_incremental_tests.rs"]
mod tests;
