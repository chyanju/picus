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
use crate::gb::model::{find_zero_cancel, FindZeroOutcome};
use crate::poly::{FfPolyRing, Poly};
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
    /// Reason cache populated by [`Theory::propagate`] so [`explain`]
    /// can recover the per-atom reason set later (mirrors
    /// `FfTheory::pending_reasons`).
    pending_reasons: HashMap<Var, Vec<(Var, bool)>>,
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

/// Outcome of [`IncrementalFfTheoryState::extract_model_via_user_ring`].
enum ModelExtraction {
    Sat(HashMap<String, BigUint>),
    Unsat,
    Unknown,
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
            pending_reasons: HashMap::new(),
        }
    }

    /// Engine telemetry from the wrapped [`IncrementalGB`]. Surfaces
    /// `pairs_generated` / `reductions_useful` for amortisation
    /// regression tests; gated by the orchestrator's `gb_stats` flag
    /// in production (a no-op when off, so this getter is safe to
    /// call unconditionally — callers must enable `gb_stats` to read
    /// non-zero counters).
    pub fn engine_stats(&self) -> &crate::ff::buchberger::GbProfileCounters {
        self.igb.engine_stats()
    }

    /// Bridge the live incremental basis to `gb::model::find_zero_cancel`
    /// against a user-namespaced ring. Slot indices in the incremental
    /// `DensePoly` exponent vectors index into a synthetic-name ring
    /// (`__slot_N`); the bridge constructs an [`FfPolyRing`] whose
    /// variable index order matches those slot positions, populated
    /// with the user's actual variable name when known and a witness
    /// placeholder otherwise. The conversion is a re-wrap (the dense
    /// flat storage is reused via `Polynomial::Dense`) plus a single
    /// `find_zero_cancel` call. Witness slots and synthetic placeholder
    /// names are filtered out of the returned model.
    fn extract_model_via_user_ring(&mut self) -> ModelExtraction {
        let basis_dense = self.igb.basis();
        if basis_dense.is_empty() {
            return ModelExtraction::Sat(HashMap::new());
        }

        // Reverse `name_to_slot`. User names go into the new ring at
        // their slot position; unclaimed positions and witness slots
        // (`__w_diseq_N`) take placeholder names that the post-filter
        // strips.
        let mut user_names: Vec<String> = (0..self.max_slots)
            .map(|i| format!("__slot_{}", i))
            .collect();
        for (name, &slot) in &self.name_to_slot {
            if !name.starts_with("__w_diseq_") && slot < self.max_slots {
                user_names[slot] = name.clone();
            }
        }

        // Rebuild a user-namespaced `FfPolyRing` with the same field
        // and slot count as the incremental ring. The default
        // `FfPolyRing::new` honours `config::poly_repr`; we pin
        // `ReprKind::Dense` because the basis polys ARE dense.
        let prime = self.atoms.prime().clone();
        let user_field = PrimeField::new(prime.clone());
        let user_ring = FfPolyRing::new_with_repr(
            user_field,
            user_names.clone(),
            picus_core::config::ReprKind::Dense,
        );

        // Re-wrap each DensePoly into `Polynomial::Dense`. Exponent
        // vectors are positional and the slot count matches, so the
        // re-wrap is structural and zero-copy at the storage layer.
        let basis_user: Vec<Poly> = basis_dense
            .into_iter()
            .map(picus_core::ff::polynomial::Polynomial::Dense)
            .collect();

        let outcome = find_zero_cancel(&user_ring, &basis_user, self.cancel);
        match outcome {
            FindZeroOutcome::Sat(raw_model) => {
                // Drop placeholder bindings before returning.
                let mut filtered: HashMap<String, BigUint> = HashMap::new();
                for (name, value) in raw_model {
                    if name.starts_with("__slot_") || name.starts_with("__w_") {
                        continue;
                    }
                    filtered.insert(name, value);
                }
                ModelExtraction::Sat(filtered)
            }
            FindZeroOutcome::Unsat => ModelExtraction::Unsat,
            FindZeroOutcome::Unknown => ModelExtraction::Unknown,
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
        // Basis is non-trivial — extract a model via `gb::model::
        // find_zero_cancel` on a user-namespaced facade ring built
        // from the live `IncrementalGB::basis()`. The bridge maps each
        // claimed slot back to its user variable name (synthetic
        // `__w_*` names for Rabinowitsch witnesses are dropped from
        // the returned model). For small primes the injected
        // `x^p − x` polynomials guarantee any common zero lies in
        // GF(p), so a Sat extraction is sound; for large primes the
        // basis only certifies a zero over the algebraic closure and
        // the model search still needs to land on a GF(p) point —
        // `find_zero_cancel` returns Unknown rather than spurious Sat
        // when its round-robin search exhausts a non-exhaustive cap,
        // so the bridge inherits that soundness gate.
        match self.extract_model_via_user_ring() {
            ModelExtraction::Sat(model) => {
                self.last_model = Some(model);
                self.has_model = true;
                CheckOutcome::Sat
            }
            ModelExtraction::Unsat => {
                self.has_model = false;
                CheckOutcome::Unsat {
                    core: self.facts.iter().map(|(v, _)| *v).collect(),
                }
            }
            ModelExtraction::Unknown => {
                // Round-robin search exhausted its bounded cap; the
                // formula could still have a model outside the searched
                // range. Sound to report Unknown.
                self.has_model = false;
                CheckOutcome::Unknown
            }
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

    fn propagate(&mut self) -> Vec<(Var, bool)> {
        self.pending_reasons.clear();
        let pinned = super::ff_theory::pinned_vars_for(self.atoms, &self.facts);
        let tier1 = super::ff_theory::compute_tier1_for(self.atoms, &self.facts, &pinned);
        let tier2 = super::ff_theory::compute_tier2_for(self.atoms, &self.facts, &pinned);
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

    fn explain(&self, atom: Var, _polarity: bool) -> Vec<(Var, bool)> {
        self.pending_reasons.get(&atom).cloned().unwrap_or_default()
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
