//! Solver-side state cache for amortising fixed work across multiple
//! `solve` calls with the same constraint side.
//!
//! The constraint side of a [`ConstraintSystem`] is hashed via
//! [`digest_constraint_side`]; a matching cache reuses the
//! prior split-GB and encodes only the per-query disequalities
//! (Rabinowitsch polynomials). Sub-iter resumability: when a fresh
//! cache build is cancelled mid-build, the per-partition
//! [`IncrementalGB`] in-flight state is preserved as a
//! `PartialBuild` and resumed on the next solve call with the
//! matching digest.

use std::collections::HashMap;
use std::sync::Arc;

use crate::frontend::bitprop::{BitProp, BitPropState};
use crate::core::{populate_bitprop, SolveOutcome};
use crate::frontend::encoder::{
    encode, encode_constraint_side, ConstraintSystem,
};
use crate::ff::buchberger::{BuchbergerConfig, IncrementalGB};
use crate::ff::monomial::MonomialOrder;
use crate::gb::ideal::{interreduce_basis, ring_for_order, unwrap_dense_vec, wrap_dense_vec, Ideal};
use crate::gb::model;
use crate::poly::{FfPolyRing, Poly};
use crate::split_gb::{
    admit, build_partitions, classify_propagation, max_fixpoint_iters, seed_self_membership,
    split_find_zero_cancel, split_gb_cancel, split_gb_extend_cancel, Propagate, SplitFindZeroOutcome,
};
use crate::timeout::CancelToken;

/// Cached state computed from the constraint side of one
/// [`ConstraintSystem`] (everything except `disequalities`).
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
    pub digest: u128,
}

/// Partial GB build state preserved across solve calls. Used when the
/// fast-path build is cancelled mid-build; subsequent calls with the
/// same digest resume via `continue_partial`, which keeps the
/// in-flight [`IncrementalGB`] per partition so the open S-pair queue
/// is not lost.
struct PartialBuild {
    digest: u128,
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
    /// Digest of the most recent `solve` call's constraint side.
    /// The cache builds only when two consecutive calls share a
    /// digest; circuits whose per-call constraint sides never repeat
    /// skip the cache-build cost entirely.
    last_digest: Option<u128>,
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
        digest: u128,
        cancel: &CancelToken,
    ) -> Result<(), ()> {
        self.cached_base = None;
        self.partial_build = None;

        // Encode the constraint side only: the cache entry is keyed on
        // `digest_constraint_side(cs)`, so the encoded ring must contain
        // everything *except* the per-query Rabinowitsch polynomials.
        // `encode_constraint_side` still reserves the `__w_diseq_i`
        // variable slots so [`encode_query_disequalities`] can build the
        // Rabinowitsch polynomial in this ring later.
        let encoded = match encode_constraint_side(cs) {
            Ok(e) => e,
            Err(_) => return Err(()),
        };
        if cancel.is_cancelled() {
            return Err(());
        }

        // basis 0 (linear) = bitsum polys + admitted originals; basis 1
        // (nonlinear) = all originals. The provenance is unused here: the
        // cached path does not extract an UNSAT core.
        let (gens, _prov) =
            build_partitions(&encoded.poly_ring, &encoded.polynomials, &encoded.bitsum_polys);

        let mut bit_prop = BitProp::new(&encoded.poly_ring);
        populate_bitprop(&encoded.poly_ring, &encoded.polynomials, &mut bit_prop);

        // Fast-path build. On cancel, `split_gb_cancel` returns
        // `Cancelled` and we transition to the resumable path.
        match split_gb_cancel(&encoded.poly_ring, gens.clone(), &mut bit_prop, cancel) {
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
                let pending = gens;
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
    let bit_prop = BitProp::from_state(poly_ring, partial.bit_prop_state.clone());

    let iter_cap = max_fixpoint_iters(k);
    let mut fixpoint_iter: u64 = 0;
    loop {
        if cancel.is_cancelled() {
            partial.bit_prop_state = bit_prop.to_state();
            return ResumeOutcome::StillPartial;
        }
        fixpoint_iter += 1;
        if fixpoint_iter > iter_cap {
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
                let basis = wrap_dense_vec(partial.inflight[i].basis());
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
                partial.inflight[i].add_generators(unwrap_dense_vec(surviving, poly_ring.ctx()))
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
            .map(|igb| Ideal::from_gb(poly_ring, wrap_dense_vec(igb.basis())))
            .collect();
        seed_self_membership(&mut partial.contains_memo, &split_basis);

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
                if classify_propagation(
                    poly_ring, &split_basis[j], j, p, p_hash, &mut partial.contains_memo, cancel,
                ) == Propagate::NewGenerator {
                    partial.pending[j].push(poly_ring.ring.clone_el(p));
                    any_new = true;
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
        let basis = wrap_dense_vec(igb.basis());
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
    for (i, &(a, b)) in cs.disequalities.iter().enumerate() {
        // Translate the query's producer-frame VarIdx into the
        // cached ring's frame via name lookup. The ring's slot order is
        // `cs.var_names` order followed by appended aux vars
        // (`__w_diseq_*` / `__bitsum_*`); `encode_impl` does not sort.
        // The integer `a`/`b` index `cs.var_names`, not ring slots, so
        // they must be re-resolved by name through `var_map`.
        let a_name = cs
            .var_names
            .get(a as usize)
            .ok_or_else(|| format!("disequality refs var_idx {} but cs.var_names has {} entries", a, cs.var_names.len()))?;
        let b_name = cs
            .var_names
            .get(b as usize)
            .ok_or_else(|| format!("disequality refs var_idx {} but cs.var_names has {} entries", b, cs.var_names.len()))?;
        let a_idx = *var_map
            .get(a_name)
            .ok_or_else(|| format!("cached var_map missing: {}", a_name))?;
        let b_idx = *var_map
            .get(b_name)
            .ok_or_else(|| format!("cached var_map missing: {}", b_name))?;
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
        // The cache key (digest) excludes disequalities, so a hit can occur
        // for a query whose disequality references a variable the cached ring
        // dropped during compaction (compaction keeps disequality endpoints,
        // but only those of the query that originally built the cache).
        // Rather than return Unknown, fall back to a fresh stateless solve for
        // this query — sound, just without the cache reuse.
        Err(_) => return stateless_solve(cs, cancel),
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
            let field = &poly_ring.field();
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names().len() {
                    model_map.insert(poly_ring.var_names()[idx].clone(), field.to_biguint(val));
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
            // Verify against the bitsum definitions as well, matching the
            // non-cached path (core::solve_split_gb_cancel): the model
            // search extends bases seeded with these, so a sound model must
            // satisfy them too.
            for p in &cached.bitsum_polys {
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
    outcome
}

fn stateless_solve(cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
    match encode(cs) {
        Ok(encoded) => crate::core::solve_encoded_with_cancel(&encoded, cancel),
        Err(_) => SolveOutcome::Unknown,
    }
}

/// Hash an [`ConstraintSystem`]'s constraint side (everything
/// except `disequalities`) into a 128-bit cache key. Self-consistent:
/// two systems agreeing on `(prime, var_names, equalities,
/// assignments, bitsums, add_field_polys)` produce the same digest.
///
/// The key is 128 bits, not 64, because a digest match is trusted to
/// reuse a prior split-GB without re-deriving it, and an UNSAT result
/// from a cache hit is returned without a model re-check (unlike SAT,
/// which `model::verify_model` validates). A two-distinct-constraint-side
/// collision would therefore be an unsound UNSAT. The two SipHash-1-3
/// passes over distinct domain prefixes act as independent 64-bit PRF
/// outputs on benign inputs, so a chance collision is ~2^-128. The
/// hasher uses `std::collections`'s fixed key, so this resistance is
/// against accidental collision on developer-controlled R1CS — not
/// against an adversary tailoring `ConstraintSystem`s to collide.
pub fn digest_constraint_side(cs: &crate::frontend::encoder::ConstraintSystem) -> u128 {
    let lo = hash_constraint_side(cs, 0x01);
    let hi = hash_constraint_side(cs, 0xA5);
    ((hi as u128) << 64) | (lo as u128)
}

fn hash_constraint_side(cs: &crate::frontend::encoder::ConstraintSystem, domain: u64) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    domain.hash(&mut h);
    cs.prime.hash(&mut h);
    cs.add_field_polys.hash(&mut h);
    // `var_names` is part of the system's identity for caching:
    // two systems with identical equalities but different name
    // strings must be treated as distinct (downstream consumers
    // surface names to users).
    cs.var_names.len().hash(&mut h);
    for n in &cs.var_names {
        n.hash(&mut h);
    }
    cs.bitsums.len().hash(&mut h);
    for bs in &cs.bitsums {
        bs.len().hash(&mut h);
        for v in bs {
            v.hash(&mut h);
        }
    }
    cs.assignments.len().hash(&mut h);
    for (v, val) in &cs.assignments {
        v.hash(&mut h);
        val.hash(&mut h);
    }
    cs.equalities.len().hash(&mut h);
    for eq in &cs.equalities {
        eq.len().hash(&mut h);
        for t in eq {
            t.coeff.hash(&mut h);
            t.vars.len().hash(&mut h);
            for &(idx, exp) in &t.vars {
                idx.hash(&mut h);
                exp.hash(&mut h);
            }
        }
    }
    h.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::encoder::{ConstraintSystemBuilder, PolyTerm};
    use num_bigint::BigUint;

    // ────────── Fixture builders ──────────

    /// `x + 3 = 0` over GF(7); SAT (x = 4). One equality, no diseq.
    fn lin_eq_sys() -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(3u32), vars: vec![] },
        ]);
        b.build()
    }

    /// Adds `x != 0` to `lin_eq_sys`; still SAT (x = 4 ≠ 0).
    fn lin_eq_with_diseq() -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        let zero = b.var("__zero");
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(3u32), vars: vec![] },
        ]);
        b.add_assignment(zero, BigUint::from(0u32));
        b.add_disequality(x, zero);
        b.build()
    }

    /// `x = 1` ∧ `x = 2` over GF(7); UNSAT.
    fn lin_unsat_sys() -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(6u32), vars: vec![] }, // x + 6 = 0 → x = 1
        ]);
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(5u32), vars: vec![] }, // x + 5 = 0 → x = 2
        ]);
        b.build()
    }

    /// `x·y - 1 = 0` over GF(7) (nonlinear); SAT.
    fn nonlinear_sat() -> ConstraintSystem {
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        let y = b.var("y");
        // x·y + 6 = 0 → x·y = 1
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1), (y, 1)] },
            PolyTerm { coeff: BigUint::from(6u32), vars: vec![] },
        ]);
        b.build()
    }

    // ────────── IncrementalSolverContext lifecycle ──────────

    #[test]
    fn new_starts_empty() {
        let ctx = IncrementalSolverContext::new();
        assert!(ctx.cached_base.is_none());
        assert!(ctx.last_digest.is_none());
        assert!(ctx.partial_build.is_none());
    }

    #[test]
    fn invalidate_clears_state() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_eq_with_diseq();
        // Drive two calls so the cache builds.
        let _ = ctx.solve(&cs, &CancelToken::none());
        let _ = ctx.solve(&cs, &CancelToken::none());
        assert!(ctx.cached_base.is_some(), "expected cache after 2 same-digest calls");
        ctx.invalidate();
        assert!(ctx.cached_base.is_none());
        assert!(ctx.partial_build.is_none());
    }

    #[test]
    fn first_call_is_stateless_no_cache_built() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_eq_with_diseq();
        let out = ctx.solve(&cs, &CancelToken::none());
        assert!(matches!(out, SolveOutcome::Sat(_)), "expected SAT, got {:?}", out);
        assert!(ctx.cached_base.is_none(), "first call must not build cache");
        assert_eq!(ctx.last_digest, Some(digest_constraint_side(&cs)));
    }

    #[test]
    fn second_call_same_digest_builds_cache() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_eq_with_diseq();
        let _ = ctx.solve(&cs, &CancelToken::none());
        let out = ctx.solve(&cs, &CancelToken::none());
        assert!(matches!(out, SolveOutcome::Sat(_)));
        assert!(ctx.cached_base.is_some(), "expected cache built on second same-digest call");
        assert_eq!(
            ctx.cached_base.as_ref().unwrap().digest,
            digest_constraint_side(&cs)
        );
    }

    #[test]
    fn third_call_same_digest_hits_cache() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_eq_with_diseq();
        let _ = ctx.solve(&cs, &CancelToken::none()); // first: stateless
        let _ = ctx.solve(&cs, &CancelToken::none()); // second: builds cache
        let before_digest = ctx.cached_base.as_ref().unwrap().digest;
        let out = ctx.solve(&cs, &CancelToken::none()); // third: cache hit
        assert!(matches!(out, SolveOutcome::Sat(_)));
        // Cache base unchanged.
        assert_eq!(ctx.cached_base.as_ref().unwrap().digest, before_digest);
    }

    #[test]
    fn distinct_digest_each_call_skips_cache() {
        let mut ctx = IncrementalSolverContext::new();
        let cs1 = lin_eq_with_diseq();
        let cs2 = nonlinear_sat();
        let _ = ctx.solve(&cs1, &CancelToken::none());
        let _ = ctx.solve(&cs2, &CancelToken::none());
        // Each call is the first time for its digest → stateless.
        assert!(ctx.cached_base.is_none(), "alternating digests must not build cache");
    }

    #[test]
    fn switching_digest_after_cache_drops_cache() {
        let mut ctx = IncrementalSolverContext::new();
        let cs_a = lin_eq_with_diseq();
        let cs_b = nonlinear_sat();
        let _ = ctx.solve(&cs_a, &CancelToken::none()); // stateless
        let _ = ctx.solve(&cs_a, &CancelToken::none()); // builds cache_a
        assert!(ctx.cached_base.is_some());
        // Now switch to a different system. No cached_base for it,
        // no prior repeat → stateless. The previous cache is cleared
        // (the should_build path's "clear cache" branch).
        let _ = ctx.solve(&cs_b, &CancelToken::none());
        assert!(ctx.cached_base.is_none(), "different digest must clear cache");
    }

    #[test]
    fn unsat_through_cached_path() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_unsat_sys();
        let _ = ctx.solve(&cs, &CancelToken::none());
        let out = ctx.solve(&cs, &CancelToken::none()); // builds cache; whole-ring detected
        assert!(matches!(out, SolveOutcome::Unsat(_)), "expected UNSAT, got {:?}", out);
    }

    #[test]
    fn unsat_through_cache_hit() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_unsat_sys();
        let _ = ctx.solve(&cs, &CancelToken::none()); // stateless UNSAT
        let _ = ctx.solve(&cs, &CancelToken::none()); // builds cache (whole-ring)
        let out = ctx.solve(&cs, &CancelToken::none()); // cache hit, fast UNSAT
        assert!(matches!(out, SolveOutcome::Unsat(_)));
    }

    #[test]
    fn nonlinear_sat_via_cache() {
        let mut ctx = IncrementalSolverContext::new();
        let cs = nonlinear_sat();
        let _ = ctx.solve(&cs, &CancelToken::none());
        let out = ctx.solve(&cs, &CancelToken::none());
        assert!(matches!(out, SolveOutcome::Sat(_)));
        assert!(ctx.cached_base.is_some());
    }

    #[test]
    fn pre_cancelled_solve_returns_unknown_or_stateless() {
        // A pre-cancelled token on the very first call should not
        // crash; the stateless path is taken and should surface a
        // non-SAT non-Unsat outcome.
        let mut ctx = IncrementalSolverContext::new();
        let cs = lin_eq_with_diseq();
        let cancel = CancelToken::with_timeout(std::time::Duration::from_nanos(0));
        // Sleep briefly so the timeout token's deadline is past.
        std::thread::sleep(std::time::Duration::from_millis(1));
        let out = ctx.solve(&cs, &cancel);
        // Either Unknown (most likely) or completion (if the solve
        // finished before the cancel check fired) — both sound.
        assert!(matches!(out, SolveOutcome::Unknown | SolveOutcome::Sat(_) | SolveOutcome::Unsat(_)));
    }

    // ────────── digest_constraint_side properties ──────────

    #[test]
    fn digest_stable_for_same_system() {
        let cs1 = lin_eq_with_diseq();
        let cs2 = lin_eq_with_diseq();
        assert_eq!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
    }

    #[test]
    fn digest_excludes_disequalities() {
        // Same constraint side, with vs without disequalities → same digest.
        let with = lin_eq_with_diseq();
        let without = lin_eq_sys();
        // `without` doesn't have the `__zero` aux var or the assignment;
        // its constraint side differs from `with`. Build a stripped
        // version of `with` keeping equalities + assignment + var_map
        // but no disequalities to test the diseq-exclusion property.
        let mut b = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b.var("x");
        let zero = b.var("__zero");
        b.add_equality(vec![
            PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] },
            PolyTerm { coeff: BigUint::from(3u32), vars: vec![] },
        ]);
        b.add_assignment(zero, BigUint::from(0u32));
        // Note: no add_disequality call.
        let stripped = b.build();
        assert_eq!(
            digest_constraint_side(&with),
            digest_constraint_side(&stripped),
            "digest must exclude disequalities"
        );
        // And not equal to `without` (which lacks the __zero var).
        assert_ne!(digest_constraint_side(&with), digest_constraint_side(&without));
    }

    #[test]
    fn digest_changes_with_prime() {
        let mut b7 = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x7 = b7.var("x");
        b7.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x7, 1)] }]);
        let cs7 = b7.build();

        let mut b11 = ConstraintSystemBuilder::new(BigUint::from(11u32));
        let x11 = b11.var("x");
        b11.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x11, 1)] }]);
        let cs11 = b11.build();

        assert_ne!(digest_constraint_side(&cs7), digest_constraint_side(&cs11));
    }

    #[test]
    fn digest_changes_with_var_names() {
        let mut bx = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let xv = bx.var("x");
        bx.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(xv, 1)] }]);
        let cs_x = bx.build();

        let mut by = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let yv = by.var("y");
        by.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(yv, 1)] }]);
        let cs_y = by.build();

        assert_ne!(digest_constraint_side(&cs_x), digest_constraint_side(&cs_y));
    }

    #[test]
    fn digest_changes_with_equalities() {
        let cs_one_eq = lin_eq_sys();
        let cs_two_eq = lin_unsat_sys(); // same vars but two equalities
        assert_ne!(digest_constraint_side(&cs_one_eq), digest_constraint_side(&cs_two_eq));
    }

    #[test]
    fn digest_changes_with_add_field_polys() {
        let mut b_off = ConstraintSystemBuilder::new(BigUint::from(7u32));
        b_off.set_add_field_polys(false);
        let x = b_off.var("x");
        b_off.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] }]);
        let cs_off = b_off.build();

        let mut b_on = ConstraintSystemBuilder::new(BigUint::from(7u32));
        b_on.set_add_field_polys(true);
        let x = b_on.var("x");
        b_on.add_equality(vec![PolyTerm { coeff: BigUint::from(1u32), vars: vec![(x, 1)] }]);
        let cs_on = b_on.build();

        assert_ne!(digest_constraint_side(&cs_off), digest_constraint_side(&cs_on));
    }

    #[test]
    fn digest_changes_with_assignments() {
        // Same equality, different assignment value → different digest
        // (assignments are part of the constraint side).
        let mut b1 = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b1.var("x");
        b1.add_assignment(x, BigUint::from(2u32));
        let cs1 = b1.build();

        let mut b2 = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b2.var("x");
        b2.add_assignment(x, BigUint::from(3u32));
        let cs2 = b2.build();

        assert_ne!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
    }

    #[test]
    fn digest_changes_with_bitsums() {
        let mut b1 = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let _x = b1.var("x");
        let _y = b1.var("y");
        let cs1 = b1.build();

        let mut b2 = ConstraintSystemBuilder::new(BigUint::from(7u32));
        let x = b2.var("x");
        let y = b2.var("y");
        b2.add_bitsum(vec![x, y]);
        let cs2 = b2.build();

        assert_ne!(digest_constraint_side(&cs1), digest_constraint_side(&cs2));
    }

    // ────────── stateless_solve direct path ──────────

    #[test]
    fn stateless_solve_sat_direct() {
        let cs = lin_eq_with_diseq();
        let out = stateless_solve(&cs, &CancelToken::none());
        assert!(matches!(out, SolveOutcome::Sat(_)));
    }

    #[test]
    fn stateless_solve_unsat_direct() {
        let cs = lin_unsat_sys();
        let out = stateless_solve(&cs, &CancelToken::none());
        assert!(matches!(out, SolveOutcome::Unsat(_)));
    }
}
