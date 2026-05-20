//! Solver-side state cache for amortising fixed work across multiple
//! `solve` calls with the same constraint side.
//!
//! The constraint side of a [`ConstraintSystem`] is hashed; a matching
//! cache reuses the prior split-GB and encodes only the per-query
//! disequalities (Rabinowitsch polynomials). Sub-iter resumability:
//! when a fresh cache build is cancelled mid-build, the per-partition
//! [`IncrementalGB`] in-flight state is preserved as a `PartialBuild`
//! and resumed on the next solve call with the matching digest.

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;

use crate::bitprop::{BitProp, BitPropState};
use crate::core::{populate_bitprop, SolveOutcome};
use crate::encoder::{encode, ConstraintSystem};
use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
use crate::ff::monomial::MonomialOrder;
use crate::ideal::{interreduce_basis, ring_for_order, Ideal};
use crate::model;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{
    admit, split_find_zero_cancel, split_gb_cancel, split_gb_extend_cancel, SplitFindZeroOutcome,
};
use crate::timeout::CancelToken;

/// Cached state computed from the constraint side of one
/// `ConstraintSystem` (everything except `disequalities`).
pub struct CachedBase {
    pub poly_ring: Arc<FfPolyRing>,
    pub var_map: HashMap<String, usize>,
    /// Polynomials encoded from equalities, assignments, bitsum-defs,
    /// and (optionally) field polys — but NOT from disequalities.
    pub constraint_polys: Vec<Poly>,
    pub bitsum_polys: Vec<Poly>,
    /// Per-partition basis polys: `split_gb_owned[0]` = linear basis,
    /// `split_gb_owned[1]` = nonlinear basis.
    pub split_gb_owned: Vec<Vec<Poly>>,
    pub bit_prop_state: BitPropState,
    pub digest: u64,
}

/// Partial GB build state preserved across solve calls. Used when the
/// fast-path build is cancelled mid-build; subsequent calls with the
/// same digest resume via `continue_partial`, which keeps the
/// in-flight [`IncrementalGB`] per partition so the open S-pair queue
/// is not lost.
struct PartialBuild {
    digest: u64,
    poly_ring: Arc<FfPolyRing>,
    var_map: HashMap<String, usize>,
    constraint_polys: Vec<Poly>,
    bitsum_polys: Vec<Poly>,
    bit_prop_state: BitPropState,
    inflight: Vec<IncrementalGB>,
    pending: Vec<Vec<Poly>>,
    contains_memo: std::collections::HashSet<(u64, usize)>,
}

#[derive(Default)]
pub struct IncrementalSolverContext {
    cached_base: Option<CachedBase>,
    /// Lazy-build flag: the first call goes through the stateless path;
    /// the cache is only built on a subsequent call whose digest matches
    /// the previous call's. Avoids paying the cache-build cost on
    /// circuits where every solve has a different constraint side.
    last_digest: Option<u64>,
    /// In-flight partial GB build saved from a cancelled call. Resumed
    /// on the next call with the same digest.
    partial_build: Option<PartialBuild>,
}

impl IncrementalSolverContext {
    pub fn new() -> Self {
        Self {
            cached_base: None,
            last_digest: None,
            partial_build: None,
        }
    }

    pub fn invalidate(&mut self) {
        self.cached_base = None;
        self.partial_build = None;
    }

    pub fn solve(&mut self, cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
        let stats_on = crate::profile::gb_stats_enabled();
        let digest = digest_constraint_side(cs);

        let cache_matches = matches!(&self.cached_base, Some(c) if c.digest == digest);
        let partial_matches = matches!(&self.partial_build, Some(p) if p.digest == digest);
        let prev_digest_matches = self.last_digest == Some(digest);
        let should_build = !cache_matches && !partial_matches && prev_digest_matches;
        self.last_digest = Some(digest);

        // First-time digest with no prior repeats: skip the cache-build
        // cost.
        if !cache_matches && !partial_matches && !should_build {
            self.cached_base = None;
            self.partial_build = None;
            return stateless_solve(cs, cancel);
        }

        // Resume an in-flight partial build.
        if !cache_matches && partial_matches {
            if stats_on {
                use std::sync::atomic::Ordering::Relaxed;
                crate::profile::NATIVE_FF
                    .cache_partial_resumes
                    .fetch_add(1, Relaxed);
            }
            let t0 = std::time::Instant::now();
            let mut partial = self.partial_build.take().unwrap();
            let outcome = continue_partial(&mut partial, cancel);
            let dt = t0.elapsed().as_nanos() as u64;
            if stats_on {
                use std::sync::atomic::Ordering::Relaxed;
                crate::profile::NATIVE_FF
                    .cache_rebuild_time_ns
                    .fetch_add(dt, Relaxed);
            }
            match outcome {
                ResumeOutcome::Complete(cached) => {
                    if stats_on {
                        use std::sync::atomic::Ordering::Relaxed;
                        crate::profile::NATIVE_FF
                            .cache_partial_completions
                            .fetch_add(1, Relaxed);
                    }
                    self.cached_base = Some(cached);
                }
                ResumeOutcome::StillPartial => {
                    self.partial_build = Some(partial);
                    return SolveOutcome::Unknown;
                }
                ResumeOutcome::Failed => {
                    return stateless_solve(cs, cancel);
                }
            }
        } else if !cache_matches {
            // Fresh build attempt via the fast path.
            if stats_on {
                use std::sync::atomic::Ordering::Relaxed;
                crate::profile::NATIVE_FF
                    .distinct_cs_digests
                    .fetch_add(1, Relaxed);
            }
            let t0 = std::time::Instant::now();
            match self.rebuild_base(cs, digest, cancel) {
                Ok(()) => {}
                Err(()) => {
                    return stateless_solve(cs, cancel);
                }
            }
            if stats_on {
                use std::sync::atomic::Ordering::Relaxed;
                let dt = t0.elapsed().as_nanos() as u64;
                crate::profile::NATIVE_FF
                    .cache_rebuild_time_ns
                    .fetch_add(dt, Relaxed);
            }
            // If the rebuild was cancelled, `rebuild_base` left
            // `partial_build` populated for resumption.
            if self.partial_build.is_some() && self.cached_base.is_none() {
                return SolveOutcome::Unknown;
            }
        } else if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            crate::profile::NATIVE_FF.cache_hits.fetch_add(1, Relaxed);
        }

        let cached = self.cached_base.as_ref().expect("cache must be built");
        let t0 = std::time::Instant::now();
        let outcome = solve_with_cached(cached, cs, cancel);
        if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            let dt = t0.elapsed().as_nanos() as u64;
            crate::profile::NATIVE_FF
                .cache_query_diff_time_ns
                .fetch_add(dt, Relaxed);
        }
        outcome
    }

    /// Build the cache via the fast path ([`split_gb_cancel`]). On
    /// cancellation, save a `PartialBuild` so the next solve call with
    /// matching digest can resume via [`continue_partial`].
    fn rebuild_base(
        &mut self,
        cs: &ConstraintSystem,
        digest: u64,
        cancel: &CancelToken,
    ) -> Result<(), ()> {
        self.cached_base = None;
        self.partial_build = None;

        let mut cs_for_cache = ConstraintSystem {
            prime: cs.prime.clone(),
            equalities: cs.equalities.clone(),
            disequalities: vec![("x0".to_string(), "x0".to_string())],
            assignments: cs.assignments.clone(),
            add_field_polys: cs.add_field_polys,
            bitsums: cs.bitsums.clone(),
        };
        if cs_for_cache
            .assignments
            .iter()
            .find(|(n, _)| n == "x0")
            .is_none()
        {
            cs_for_cache
                .assignments
                .insert(0, ("x0".to_string(), num_bigint::BigUint::from(1u32)));
        }

        let mut encoded = match encode(&cs_for_cache) {
            Ok(e) => e,
            Err(_) => return Err(()),
        };
        if !encoded.polynomials.is_empty() {
            encoded.polynomials.pop();
        }
        if cancel.is_cancelled() {
            return Err(());
        }

        let nl_gens: Vec<Poly> = encoded
            .polynomials
            .iter()
            .map(|p| encoded.poly_ring.ring.clone_el(p))
            .collect();
        let mut l_gens: Vec<Poly> = Vec::new();
        for p in &encoded.bitsum_polys {
            l_gens.push(encoded.poly_ring.ring.clone_el(p));
        }
        for p in &encoded.polynomials {
            if admit(&encoded.poly_ring, 0, p) {
                l_gens.push(encoded.poly_ring.ring.clone_el(p));
            }
        }

        let mut bit_prop = BitProp::new(&encoded.poly_ring);
        populate_bitprop(&encoded.poly_ring, &encoded.polynomials, &mut bit_prop);

        // Fast-path build. On cancel, `split_gb_cancel` returns
        // `Cancelled` and we transition to the resumable path.
        match split_gb_cancel(
            &encoded.poly_ring,
            vec![l_gens.clone(), nl_gens.clone()],
            &mut bit_prop,
            cancel,
        ) {
            Ok(split_basis) => {
                let split_gb_owned: Vec<Vec<Poly>> = split_basis
                    .into_iter()
                    .map(|ideal| {
                        ideal
                            .basis
                            .iter()
                            .map(|p| encoded.poly_ring.ring.clone_el(p))
                            .collect()
                    })
                    .collect();
                let bit_prop_state = bit_prop.to_state();
                self.cached_base = Some(CachedBase {
                    poly_ring: Arc::new(encoded.poly_ring),
                    var_map: encoded.var_map,
                    constraint_polys: encoded.polynomials,
                    bitsum_polys: encoded.bitsum_polys,
                    split_gb_owned,
                    bit_prop_state,
                    digest,
                });
                Ok(())
            }
            Err(_) => {
                // Build was cancelled. Save the encoding artifacts plus
                // initial generators as a `PartialBuild` so the next
                // call can resume via `continue_partial`. The S-pair
                // work from this attempt is lost (the IGBs inside
                // `split_gb_cancel` are dropped); subsequent resume
                // calls accumulate progress.
                let ring = ring_for_order(&encoded.poly_ring, MonomialOrder::DegRevLex);
                let cfg = BuchbergerConfig {
                    order: MonomialOrder::DegRevLex,
                    cancel_token: None,
                    abort_on_trivial: true,
                    use_f4: crate::ff::buchberger::use_f4_default(),
                };
                let inflight = vec![
                    IncrementalGB::new(ring.clone(), cfg.clone()),
                    IncrementalGB::new(ring, cfg),
                ];
                let pending = vec![l_gens, nl_gens];
                let bit_prop_state = bit_prop.to_state();
                self.partial_build = Some(PartialBuild {
                    digest,
                    poly_ring: Arc::new(encoded.poly_ring),
                    var_map: encoded.var_map,
                    constraint_polys: encoded.polynomials,
                    bitsum_polys: encoded.bitsum_polys,
                    bit_prop_state,
                    inflight,
                    pending,
                    contains_memo: std::collections::HashSet::new(),
                });
                // Returning Ok here lets the caller know the rebuild
                // attempt is captured (in partial_build); the solve()
                // entry point will return Unknown for this query.
                Ok(())
            }
        }
    }
}

enum ResumeOutcome {
    Complete(CachedBase),
    StillPartial,
    Failed,
}

/// Resume a partial build. Re-attaches the new cancel token to all
/// in-flight `IncrementalGB`s, runs the fixpoint loop. On completion,
/// produces a `CachedBase`. On further cancellation, the partial state
/// is updated in place and `StillPartial` is returned.
fn continue_partial(partial: &mut PartialBuild, cancel: &CancelToken) -> ResumeOutcome {
    for igb in partial.inflight.iter_mut() {
        igb.set_cancel_token(Some(cancel.clone()));
    }
    let poly_ring: &FfPolyRing = &partial.poly_ring;
    let k = partial.inflight.len();
    let mut bit_prop = BitProp::from_state(poly_ring, partial.bit_prop_state.clone());

    let max_fixpoint_iters = (k * 64).max(256);
    let mut fixpoint_iter: u64 = 0;
    loop {
        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        fixpoint_iter += 1;
        if fixpoint_iter > max_fixpoint_iters as u64 {
            log::warn!("continue_partial: fixpoint cap reached");
            break;
        }

        let mut any_extend_work = false;
        for i in 0..k {
            if cancel.is_cancelled() {
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }
            let pending_i = std::mem::take(&mut partial.pending[i]);
            let has_pending = !pending_i.is_empty();
            let has_open = !partial.inflight[i].is_quiescent();
            if !has_pending && !has_open {
                continue;
            }
            any_extend_work = true;
            let surviving: Vec<Poly> = if has_pending {
                let basis = partial.inflight[i].basis();
                if basis.is_empty() {
                    pending_i
                } else {
                    let basis_refs: Vec<&Poly> = basis.iter().collect();
                    let ring = poly_ring.ctx();
                    pending_i
                        .into_iter()
                        .map(|p| p.reduce_by_refs_cancel(&basis_refs, ring, cancel))
                        .filter(|p| !p.is_zero())
                        .collect()
                }
            } else {
                Vec::new()
            };
            if cancel.is_cancelled() {
                partial.pending[i] = surviving;
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }

            let res = if !surviving.is_empty() {
                partial.inflight[i].add_generators(surviving)
            } else {
                partial.inflight[i].run_only()
            };
            if res.is_err() {
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }
        }

        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        if partial.inflight.iter().any(|igb| igb.is_trivial()) {
            break;
        }

        let split_basis: Vec<Ideal> = partial
            .inflight
            .iter()
            .map(|igb| Ideal::from_gb(poly_ring, igb.basis()))
            .collect();
        for j in 0..k {
            for p in &split_basis[j].basis {
                partial.contains_memo.insert((p.content_hash(), j));
            }
        }

        let mut to_propagate =
            bit_prop.get_bit_equalities_with_cancel(&split_basis, Some(cancel));
        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        for b in &split_basis {
            for p in &b.basis {
                to_propagate.push(poly_ring.ring.clone_el(p));
            }
        }

        let mut any_new = false;
        for p in &to_propagate {
            if cancel.is_cancelled() {
                partial.bit_prop_state = bit_prop.to_state();
                return ResumeOutcome::StillPartial;
            }
            let p_hash = p.content_hash();
            for j in 0..k {
                if admit(poly_ring, j, p) {
                    let key = (p_hash, j);
                    if partial.contains_memo.contains(&key) {
                        continue;
                    }
                    let in_basis = split_basis[j].contains_with_cancel(p, cancel);
                    if in_basis {
                        partial.contains_memo.insert(key);
                    } else {
                        partial.pending[j].push(poly_ring.ring.clone_el(p));
                        any_new = true;
                        partial.contains_memo.insert(key);
                    }
                }
            }
        }

        if !any_new && !any_extend_work {
            break;
        }
        if !any_new {
            continue;
        }
    }

    if partial.inflight.iter().all(|igb| igb.is_quiescent())
        && partial.pending.iter().all(|p| p.is_empty())
    {
        // Build the CachedBase. Take ownership of all the partial's
        // fields via std::mem::replace.
        let dummy_partial = PartialBuild {
            digest: 0,
            poly_ring: partial.poly_ring.clone(),
            var_map: HashMap::new(),
            constraint_polys: Vec::new(),
            bitsum_polys: Vec::new(),
            bit_prop_state: partial.bit_prop_state.clone(),
            inflight: Vec::new(),
            pending: Vec::new(),
            contains_memo: std::collections::HashSet::new(),
        };
        let owned = std::mem::replace(partial, dummy_partial);
        match finalize_partial(owned) {
            Some(c) => ResumeOutcome::Complete(c),
            None => ResumeOutcome::Failed,
        }
    } else {
        partial.bit_prop_state = bit_prop.to_state();
        ResumeOutcome::StillPartial
    }
}

/// Convert a quiescent partial build into a `CachedBase`. Performs a
/// final inter-reduce on each partition's basis to produce the
/// canonical reduced GB.
fn finalize_partial(partial: PartialBuild) -> Option<CachedBase> {
    let cancel = CancelToken::none();
    let poly_ring: &FfPolyRing = &partial.poly_ring;
    let mut split_gb_owned: Vec<Vec<Poly>> = Vec::with_capacity(partial.inflight.len());
    for igb in partial.inflight.iter() {
        let basis = igb.basis();
        let reduced = interreduce_basis(poly_ring, basis, &cancel);
        split_gb_owned.push(reduced);
    }
    Some(CachedBase {
        poly_ring: partial.poly_ring,
        var_map: partial.var_map,
        constraint_polys: partial.constraint_polys,
        bitsum_polys: partial.bitsum_polys,
        split_gb_owned,
        bit_prop_state: partial.bit_prop_state,
        digest: partial.digest,
    })
}

fn encode_query_disequalities(
    cs: &ConstraintSystem,
    poly_ring: &FfPolyRing,
    var_map: &HashMap<String, usize>,
) -> Result<Vec<Poly>, String> {
    let mut out = Vec::with_capacity(cs.disequalities.len());
    for (i, (a, b)) in cs.disequalities.iter().enumerate() {
        let a_idx = *var_map
            .get(a)
            .ok_or_else(|| format!("cached var_map missing: {}", a))?;
        let b_idx = *var_map
            .get(b)
            .ok_or_else(|| format!("cached var_map missing: {}", b))?;
        let w_name = format!("__w_diseq_{}", i);
        let w_idx = *var_map
            .get(&w_name)
            .ok_or_else(|| format!("cached var_map missing: {}", w_name))?;
        let diff = poly_ring.sub(poly_ring.var(a_idx), poly_ring.var(b_idx));
        let prod = poly_ring.mul(diff, poly_ring.var(w_idx));
        let rabinowitsch = poly_ring.sub(prod, poly_ring.one());
        out.push(rabinowitsch);
    }
    Ok(out)
}

fn solve_with_cached(
    cached: &CachedBase,
    cs: &ConstraintSystem,
    cancel: &CancelToken,
) -> SolveOutcome {
    let poly_ring: &FfPolyRing = &cached.poly_ring;

    let query_polys = match encode_query_disequalities(cs, poly_ring, &cached.var_map) {
        Ok(polys) => polys,
        Err(_) => return SolveOutcome::Unknown,
    };

    let starting: Vec<Ideal> = cached
        .split_gb_owned
        .iter()
        .map(|polys| {
            let cloned: Vec<Poly> = polys
                .iter()
                .map(|p| poly_ring.ring.clone_el(p))
                .collect();
            Ideal::from_gb(poly_ring, cloned)
        })
        .collect();

    let k = starting.len();
    let mut new_polys_per_split: Vec<Vec<Poly>> = (0..k).map(|_| Vec::new()).collect();
    for p in &query_polys {
        let mut placed = false;
        if k > 0 && admit(poly_ring, 0, p) {
            new_polys_per_split[0].push(poly_ring.ring.clone_el(p));
            placed = true;
        }
        if k > 1 {
            new_polys_per_split[1].push(poly_ring.ring.clone_el(p));
            placed = true;
        }
        if !placed && k > 0 {
            new_polys_per_split[0].push(poly_ring.ring.clone_el(p));
        }
    }

    let mut bit_prop = BitProp::from_state(poly_ring, cached.bit_prop_state.clone());

    let new_basis = match split_gb_extend_cancel(
        poly_ring,
        starting,
        new_polys_per_split,
        &mut bit_prop,
        cancel,
    ) {
        Ok(b) => b,
        Err(_) => return SolveOutcome::Unknown,
    };

    if new_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat(
            (0..cached.constraint_polys.len() + query_polys.len()).collect(),
        );
    }

    let outcome = match split_find_zero_cancel(poly_ring, new_basis, &mut bit_prop, cancel) {
        Ok(SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field;
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names.len() {
                    model_map.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
                }
            }
            let mut full_polys: Vec<Poly> = cached
                .constraint_polys
                .iter()
                .map(|p| poly_ring.ring.clone_el(p))
                .collect();
            for p in &query_polys {
                full_polys.push(poly_ring.ring.clone_el(p));
            }
            if model::verify_model(poly_ring, &full_polys, &model_map) {
                SolveOutcome::Sat(model_map)
            } else {
                SolveOutcome::Unknown
            }
        }
        Ok(SplitFindZeroOutcome::Unsat) => {
            SolveOutcome::Unsat((0..cached.constraint_polys.len() + query_polys.len()).collect())
        }
        Ok(SplitFindZeroOutcome::Unknown) => SolveOutcome::Unknown,
        Err(_) => SolveOutcome::Unknown,
    };
    let _ = outcome.clone();
    outcome
}

fn stateless_solve(cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
    match encode(cs) {
        Ok(encoded) => crate::core::solve_encoded_with_cancel(&encoded, cancel),
        Err(_) => SolveOutcome::Unknown,
    }
}

pub fn digest_constraint_side(cs: &ConstraintSystem) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    cs.prime.hash(&mut h);
    cs.add_field_polys.hash(&mut h);
    cs.bitsums.len().hash(&mut h);
    for bs in &cs.bitsums {
        bs.len().hash(&mut h);
        for v in bs {
            v.hash(&mut h);
        }
    }
    cs.assignments.len().hash(&mut h);
    for (n, v) in &cs.assignments {
        n.hash(&mut h);
        v.hash(&mut h);
    }
    cs.equalities.len().hash(&mut h);
    for eq in &cs.equalities {
        eq.len().hash(&mut h);
        for t in eq {
            t.coeff.hash(&mut h);
            t.vars.len().hash(&mut h);
            for v in &t.vars {
                v.hash(&mut h);
            }
        }
    }
    h.finish()
}

#[allow(dead_code)]
fn _unused() -> BigUint {
    BigUint::from(0u32)
}
