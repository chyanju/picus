//! FF theory plug-in over `core::solve_encoded_with_cancel`.
//!
//! Shape matches cvc5's FF sub-theory. Facts arrive via
//! [`Theory::notify_fact`] onto a level-indexed trail. Each
//! [`Theory::post_check`] walks the trail
//! through [`ConstraintSystemBuilder`] to build a canonical
//! [`ConstraintSystem`], runs the GB solver via
//! [`encode`], and maps any returned UNSAT core indices
//! back to atom variables. Each `AtomKey` carries its terms and
//! interns them into the builder via `AtomKey::intern_into`.

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::Zero;

use crate::core::{solve_encoded_with_cancel, SolveOutcome};
use crate::frontend::encoder::{encode, ConstraintSystemBuilder, EncodedSystem, PolySource, PolyTerm};
use crate::sat::Var;
use crate::timeout::CancelToken;

use super::atoms::AtomTable;
use super::theory::{CheckOutcome, Theory};

/// FF theory plug-in: maintains an asserted-fact trail and dispatches
/// `post_check` to [`solve_encoded_with_cancel`].
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

    /// Build a `ConstraintSystem` from the trail via
    /// `ConstraintSystemBuilder`, encode, dispatch to the GB solver,
    /// and map any returned core polynomial indices back to atom
    /// variables. The mapping uses `EncodedSystem::poly_provenance`
    /// (per-polynomial source tags) rather than positional layout, so
    /// it is robust to the encoder's interleaving of assignment /
    /// Rabinowitsch / field polynomials and to dropped zero
    /// polynomials.
    fn check_full_with_mapping(&mut self) -> CheckOutcome {
        let prime = self.atoms.prime().clone();

        let mut builder = ConstraintSystemBuilder::new(prime.clone());
        // Match the GB-direct path (`PolyIR::to_constraint_system`):
        // request field polynomials `x^p - x = 0` for small primes.
        // `encode` only materialises them when `prime <= 1000`, so this
        // is a no-op for BN128 but essential for small-prime fields
        // (GF(7)/GF(11)) — without it the per-branch GB can't model the
        // field and returns Unknown instead of the real counter-example.
        builder.set_add_field_polys(prime <= BigUint::from(1000u32));
        let mut equality_atoms: Vec<Var> = Vec::new();
        let mut disequality_atoms: Vec<Var> = Vec::new();
        let mut diseq_counter: usize = 0;
        let mut zero_idx: Option<u32> = None;
        let mut had_any = false;

        for &(atom_var, polarity) in &self.facts {
            let key = match self.atoms.atom(atom_var) {
                Some(k) => k,
                None => continue,
            };
            had_any = true;
            if polarity {
                let terms = key.intern_into(&mut builder);
                builder.add_equality(terms);
                equality_atoms.push(atom_var);
            } else {
                let (d_idx, zero) =
                    builder.fresh_disequality_vars(&mut diseq_counter, &mut zero_idx);

                // Encode `(d - lhs) = 0`: starts with `+1 * d_var`
                // then appends the atom's polynomial with each coeff
                // negated mod prime.
                let mut def: Vec<PolyTerm> = Vec::with_capacity(key.terms.len() + 1);
                def.push(PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(d_idx, 1)],
                });
                def.extend(key.intern_negated_into(&mut builder, &prime));
                builder.add_equality(def);
                equality_atoms.push(atom_var);
                builder.add_disequality(d_idx, zero);
                disequality_atoms.push(atom_var);
            }
        }

        if !had_any {
            self.last_model = Some(HashMap::new());
            self.has_model = true;
            return CheckOutcome::Sat;
        }

        let indexed = builder.build();
        let encoded = match encode(&indexed) {
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
                match map_core_to_atoms(
                    &core_indices,
                    &encoded,
                    &equality_atoms,
                    &disequality_atoms,
                ) {
                    Some(core) => CheckOutcome::Unsat { core },
                    None => CheckOutcome::Unknown,
                }
            }
            SolveOutcome::Unknown => {
                self.has_model = false;
                CheckOutcome::Unknown
            }
        }
    }

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
            let inv_a = match super::field_inverse(&unpinned_coeff, prime) {
                Some(i) => i,
                None => continue,
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

/// Map a theory UNSAT core (polynomial indices into `encoded`) back to the
/// trail atom variables responsible, via per-polynomial provenance.
///
/// `Equality(j)` is reliable only when the pre-encode rewrite dropped no
/// equality — detected by `encoded.n_input_equalities == equality_atoms.len()`;
/// otherwise a specific equality cannot be pinned and the whole trail is
/// returned. `Rabinowitsch(d)` always aligns (disequalities are never dropped
/// or reordered). `Other` / unattributable polynomials (zero assignment, field
/// polys) contribute no removable atom.
///
/// Returns the sorted, deduped core — the precise atom set, or the full trail
/// when a core index cannot be attributed — or `None` when even the full-trail
/// fallback is empty (the caller then reports Unknown).
fn map_core_to_atoms(
    core_indices: &[usize],
    encoded: &EncodedSystem,
    equality_atoms: &[Var],
    disequality_atoms: &[Var],
) -> Option<Vec<Var>> {
    let eq_aligned = encoded.n_input_equalities == equality_atoms.len();
    let mut atom_core: Vec<Var> = Vec::new();
    let mut need_full = false;
    for &i in core_indices {
        match encoded.poly_provenance.get(i) {
            Some(PolySource::Equality(j)) => match (eq_aligned, equality_atoms.get(*j)) {
                (true, Some(&av)) => atom_core.push(av),
                _ => need_full = true,
            },
            Some(PolySource::Rabinowitsch(d)) => match disequality_atoms.get(*d) {
                Some(&av) => atom_core.push(av),
                None => need_full = true,
            },
            Some(PolySource::Other) | None => {}
        }
    }
    if !need_full {
        atom_core.sort();
        atom_core.dedup();
    }
    if need_full || atom_core.is_empty() {
        // Coarser but sound: the whole trail is inconsistent (the GB proved
        // UNSAT over all asserted facts). Used when a core index cannot be
        // precisely attributed, or when only encoder-internal polynomials
        // were named.
        let mut full: Vec<Var> = equality_atoms.to_vec();
        full.extend_from_slice(disequality_atoms);
        full.sort();
        full.dedup();
        if full.is_empty() {
            return None;
        }
        return Some(full);
    }
    Some(atom_core)
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

    fn post_check(&mut self) -> CheckOutcome {
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

    fn collect_model(&self) -> Option<HashMap<String, BigUint>> {
        if self.has_model {
            self.last_model.clone()
        } else {
            None
        }
    }
}

#[cfg(test)]
#[path = "ff_theory_tests.rs"]
mod tests;
