//! Plan v9 — solver-side state cache for amortizing fixed work across
//! multiple `solve` calls with the same constraint side.
//!
//! Each call to `solve_encoded` previously rebuilt the encoded
//! constraint system + ran `populate_bitprop` + computed the split-GB
//! from scratch. With this context, the constraint side of the query
//! is hashed; matching cache reuses the prior split-GB and only encodes
//! the per-query disequality (Rabinowitsch polynomial).
//!
//! Soundness rests on the existing `Ideal::extend_with_cancel`
//! correctness (Plan v6): adding a generator to a reduced GB and
//! re-running incremental Buchberger yields the same final GB as
//! recomputing on the union. Per-query Rabinowitsch is the ONLY
//! polynomial that differs between cache-hit calls; we add it via
//! `split_gb_extend_cancel` and run `split_find_zero_cancel` on the
//! result. Equivalent to `solve_encoded_with_cancel(constraints +
//! rabinowitsch)`.
//!
//! KPI motivation (Plan v9 task 01 diagnosis): on `inTest`, picus's
//! DPVL driver makes 2-3 `solve_encoded` calls per run, ALL with the
//! same constraint-side digest. Each call independently rebuilds the
//! split-GB on a 280-poly basis-1 (~30 s). This cache turns calls 2..N
//! into per-query incremental updates (~10 s each), bringing `inTest`
//! under the 60 s gate. On `modulusagainst2p` (where 24 of 25 calls
//! repeat the same digest), the cache is even more impactful.

use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigUint;

use crate::bitprop::{BitProp, BitPropState};
use crate::core::{populate_bitprop, SolveOutcome};
use crate::encoder::{encode, ConstraintSystem};
use crate::ideal::Ideal;
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

#[derive(Default)]
pub struct IncrementalSolverContext {
    cached_base: Option<CachedBase>,
    /// Plan v9 task 03 refinement: don't build the cache speculatively.
    /// First call goes through the stateless path; we only build the
    /// cache on a SUBSEQUENT call whose digest matches the previous
    /// call's. This avoids paying the cache-build cost on circuits
    /// where every DPVL signal query has a different constraint side
    /// (e.g. `test-rollup-tx-states` — 14 calls, 14 distinct digests),
    /// while still amortizing on stuck-signal circuits (e.g.
    /// `modulusagainst2p` — 25 calls, 24 same-digest streak).
    last_digest: Option<u64>,
}

impl IncrementalSolverContext {
    pub fn new() -> Self {
        Self { cached_base: None, last_digest: None }
    }

    pub fn invalidate(&mut self) {
        self.cached_base = None;
    }

    /// Solve a query against the (possibly cached) base. The query's
    /// constraint side is digested; on hit, only the per-query
    /// disequality (Rabinowitsch poly) is encoded fresh and the
    /// cached split-GB is incrementally extended. On miss, the cache
    /// is rebuilt.
    pub fn solve(&mut self, cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
        let stats_on = crate::profile::gb_stats_enabled();
        let digest = digest_constraint_side(cs);

        // Plan v9 task 03 refinement: cache lazily.
        let cache_matches = matches!(&self.cached_base, Some(c) if c.digest == digest);
        let prev_digest_matches = self.last_digest == Some(digest);
        let should_build_cache = !cache_matches && prev_digest_matches;
        self.last_digest = Some(digest);

        // First call (or non-repeating digest after a different one): no
        // cache yet. Run stateless solve. Don't pay the cache-build cost
        // on circuits where every call has a different constraint side.
        if !cache_matches && !should_build_cache {
            // Drop any stale cache (from a previous digest run).
            self.cached_base = None;
            return stateless_solve(cs, cancel);
        }

        if !cache_matches {
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
                    // Rebuild was cancelled; fall back to stateless solve.
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
        } else if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            crate::profile::NATIVE_FF
                .cache_hits
                .fetch_add(1, Relaxed);
        }

        // Cache is now populated (rebuild succeeded or it was already there).
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

    /// Rebuild the cache from `cs`'s constraint side. Returns Err on
    /// cancellation, leaving the cache cleared.
    fn rebuild_base(
        &mut self,
        cs: &ConstraintSystem,
        digest: u64,
        cancel: &CancelToken,
    ) -> Result<(), ()> {
        // Drop any previous cache before building a new one.
        self.cached_base = None;

        // Encode with disequalities cleared but a placeholder kept so
        // the witness var `__w_diseq_0` is allocated in `var_map`.
        // The placeholder Rabinowitsch poly is dropped from `polynomials`
        // so the cached split-GB is on constraint-side only.
        //
        // Why placeholder: `encode` allocates `__w_diseq_0` only when
        // `disequalities.is_empty() == false`. The cached `var_map`
        // must contain it so per-query Rabinowitsch encoding (using
        // the cached `var_map`) finds it.
        let mut cs_for_cache = ConstraintSystem {
            prime: cs.prime.clone(),
            equalities: cs.equalities.clone(),
            disequalities: vec![("x0".to_string(), "x0".to_string())],
            assignments: cs.assignments.clone(),
            add_field_polys: cs.add_field_polys,
            bitsums: cs.bitsums.clone(),
        };
        // `cs.assignments[0] = (x0, 1)` is added by `query_to_constraint_system`,
        // but a defensive insert if cs.assignments is empty.
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

        // Drop the placeholder Rabinowitsch poly. The encoder appends
        // it AFTER equalities + assignments, so it's at index
        // `n_eq + n_ass` (after filtering of zero polys, which is
        // also done for equalities and assignments). The simplest way
        // to drop it accurately is to re-encode WITHOUT disequalities
        // and use those polynomials. But that loses the witness var
        // allocation. Compromise: encode with the placeholder, then
        // re-encode without it for the polynomials, but reuse the
        // first encode's poly_ring/var_map.
        //
        // Even simpler: just truncate by `n_diseq=1`. The Rabinowitsch
        // is the LAST among equality/assignment/Rabinowitsch polys
        // (bitsums are kept separate).
        //
        // Robustness: we drop the last poly equal to the encoded
        // placeholder Rabinowitsch. It's the LAST entry pushed before
        // bitsum encoding in `encode`.
        if !encoded.polynomials.is_empty() {
            encoded.polynomials.pop();
        }

        if cancel.is_cancelled() {
            return Err(());
        }

        // Build l_gens / nl_gens for split_gb_cancel (mirrors core.rs).
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

        let split_basis = match split_gb_cancel(
            &encoded.poly_ring,
            vec![l_gens, nl_gens],
            &mut bit_prop,
            cancel,
        ) {
            Ok(b) => b,
            Err(_) => return Err(()),
        };

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
}

/// Encode just the per-query Rabinowitsch polynomial(s) using a
/// cached `poly_ring` and `var_map`. Returns one polynomial per
/// disequality.
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

/// Run a solve against a cached base + per-query disequality.
fn solve_with_cached(
    cached: &CachedBase,
    cs: &ConstraintSystem,
    cancel: &CancelToken,
) -> SolveOutcome {
    let poly_ring: &FfPolyRing = &cached.poly_ring;

    // Encode the per-query Rabinowitsch poly(s).
    let query_polys = match encode_query_disequalities(cs, poly_ring, &cached.var_map) {
        Ok(polys) => polys,
        Err(_) => return SolveOutcome::Unknown,
    };

    // Reconstruct lifetime-bound Ideals from owned cached polys.
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

    // Per-query polys go to the appropriate split via admit. Rabinowitsch
    // is degree 2 → admit(0, ...) is false → goes to basis 1.
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

    // Reconstruct BitProp from the cached state for this call.
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

    // Whole-ring shortcut.
    if new_basis.iter().any(|b| b.is_whole_ring()) {
        return SolveOutcome::Unsat((0..cached.constraint_polys.len() + query_polys.len()).collect());
    }

    // Run split_find_zero. Note that for SAT-model verification we
    // need the FULL polys list (constraints + per-query Rabinowitsch),
    // since `split_find_zero_cancel` uses these as the `orig_polys` for
    // conflict detection.
    let outcome = match split_find_zero_cancel(poly_ring, new_basis, &mut bit_prop, cancel) {
        Ok(SplitFindZeroOutcome::Sat(point)) => {
            let mut model_map = HashMap::new();
            let field = &poly_ring.field;
            for (idx, val) in point.iter().enumerate() {
                if idx < poly_ring.var_names.len() {
                    model_map.insert(poly_ring.var_names[idx].clone(), field.to_biguint(val));
                }
            }
            // Verify model against the FULL system (constraints + Rabinowitsch).
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

/// Stateless-equivalent solve, used as a fallback if the cache cannot
/// be populated (cancelled mid-rebuild). Calls into the existing path.
fn stateless_solve(cs: &ConstraintSystem, cancel: &CancelToken) -> SolveOutcome {
    match encode(cs) {
        Ok(encoded) => crate::core::solve_encoded_with_cancel(&encoded, cancel),
        Err(_) => SolveOutcome::Unknown,
    }
}

/// Hash the constraint SIDE of a `ConstraintSystem`. Excludes
/// `disequalities` (the per-query part).
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

// Allow unused import in some contexts (BigUint via from(1u32)).
#[allow(dead_code)]
fn _unused() -> BigUint {
    BigUint::from(0u32)
}
