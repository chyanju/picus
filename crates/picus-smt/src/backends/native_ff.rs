//! Native Rust finite-field solver backend — a pure-Rust replacement
//! for the cvc5 QF_FF theory solver.
//!
//! Consumes a [`PolyIR`] snapshot directly: each polynomial equality is
//! translated into a `Vec<PolyTerm>` summed to zero, and the target
//! disequality `x_target ≠ y_target` is handed to the GB solver via
//! the Rabinowitsch trick wired into [`IncrementalSolverContext`].

use num_bigint::BigUint;

use crate::backends::{SolverBackend, SolverBackendDescriptor, SolverError, SolverResult, UnknownReason};
use crate::poly_ir::PolyIR;
use crate::Theory;

use picus_solver::core::{solve_encoded_with_cancel, SolveOutcome};
use picus_solver::encoder::{
    encode, ConstraintSystem, ConstraintSystemBuilder, IndexedConstraintSystem, IndexedTerm,
};
use picus_solver::incremental_context::IncrementalSolverContext;
use picus_solver::timeout::CancelToken;

pub struct NativeFfBackend {
    /// Constraint-side digest of the most recent `solve` call. Used to
    /// count consecutive-same-digest streaks for telemetry.
    last_cs_digest: Option<u64>,
    /// Amortises split-GB across `solve` calls whose constraint side
    /// has not changed. Whether to actually consult it is read from
    /// `RuntimeConfig::cache_enabled` at each `solve` call rather than
    /// cached on the struct, so a `ConfigGuard` override applies
    /// immediately to in-flight backend instances.
    cache: IncrementalSolverContext,
}

impl Default for NativeFfBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeFfBackend {
    pub fn new() -> Self {
        NativeFfBackend {
            last_cs_digest: None,
            cache: IncrementalSolverContext::new(),
        }
    }
}

/// Thin wrapper around the cache module's
/// `digest_indexed_constraint_side`. Used for the stats path's
/// `last_cs_digest` tracking; the cache itself still keys on the
/// legacy String-keyed digest until A9 unifies the two paths.
fn digest_native_constraint_side(ics: &IndexedConstraintSystem) -> u64 {
    picus_solver::incremental_context::digest_indexed_constraint_side(ics)
}

/// Lower a `PolyIR` to an [`IndexedConstraintSystem`] via the
/// `ConstraintSystemBuilder`. Each polynomial equality becomes one
/// `Vec<IndexedTerm>` summing to zero; the target disequality
/// lifts to the system's `disequalities` slot.
///
/// The builder interns variable names in `PolyIR` ring order, so
/// the resulting `var_names` mirrors `ir.ring.ring.var_names()`
/// exactly. Term emission uses `poly_terms_idx` which yields
/// `(ring_var_idx, exponent)` directly — no per-monomial String
/// allocation.
fn ir_to_indexed_constraint_system(ir: &PolyIR) -> IndexedConstraintSystem {
    let prime = ir.ring.field.prime().clone();
    let mut builder = ConstraintSystemBuilder::new(prime.clone());

    // Pre-intern every ring variable in PolyIR's own order so
    // builder indices == ring indices, allowing direct use of
    // `poly_terms_idx`'s output.
    for name in ir.ring.ring.var_names() {
        builder.var(name);
    }

    for poly in &ir.equalities {
        let terms: Vec<IndexedTerm> = ir
            .poly_terms_idx(poly)
            .filter(|(coeff, _)| !coeff_is_zero(coeff))
            .map(|(coeff, vars)| IndexedTerm {
                coeff,
                vars: vars
                    .into_iter()
                    .map(|(v, e)| (v as u32, e))
                    .collect(),
            })
            .collect();
        if !terms.is_empty() {
            builder.add_equality(terms);
        }
    }

    // Target disequality: x_target ≠ y_target. Ring indices: target
    // is `target_signal`; alt copy lives at `n_wires + target_signal`.
    let x_idx = ir.target_signal as u32;
    let y_idx = (ir.n_wires + ir.target_signal) as u32;
    builder.add_disequality(x_idx, y_idx);

    // Field polynomials `x^p - x = 0` are essential for sound GB
    // reasoning over small primes (otherwise the GB engine treats `x`
    // as ranging over the algebraic closure, not GF(p)), but are
    // prohibitively expensive for cryptographic primes. The encoder
    // refuses to materialise them past `prime > 1000` anyway, so
    // mirror its gate here.
    let small_prime_threshold = num_bigint::BigUint::from(1000u32);
    builder.set_add_field_polys(prime <= small_prime_threshold);

    builder.build()
}

/// Bridge wrapper: lowers `PolyIR` through the index-keyed builder
/// then converts to the legacy String-keyed `ConstraintSystem` for
/// consumers (cache, legacy `encode`, digest) that have not yet been
/// migrated. Removed in phase 7A9 once every consumer accepts
/// `IndexedConstraintSystem` directly.
fn ir_to_constraint_system(ir: &PolyIR) -> ConstraintSystem {
    ir_to_indexed_constraint_system(ir).to_legacy()
}

fn coeff_is_zero(c: &BigUint) -> bool {
    use num_traits::Zero;
    c.is_zero()
}

impl SolverBackend for NativeFfBackend {
    fn solve(
        &mut self,
        ir: &PolyIR,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError> {
        if cancel.is_cancelled() {
            return Ok(SolverResult::Unknown(UnknownReason::Timeout));
        }
        let indexed = ir_to_indexed_constraint_system(ir);
        let cs = indexed.to_legacy();
        let stats_on = picus_solver::profile::gb_stats_enabled();
        let cs_digest = if stats_on {
            Some(digest_native_constraint_side(&indexed))
        } else {
            None
        };
        if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            let nf = &picus_solver::profile::NATIVE_FF;
            nf.solve_calls.fetch_add(1, Relaxed);
            if let Some(d) = cs_digest {
                if self.last_cs_digest == Some(d) {
                    nf.repeated_cs_digest_streak.fetch_add(1, Relaxed);
                }
                // `distinct_cs_digests` is incremented inside
                // `IncrementalSolverContext::solve` on rebuild — single
                // source of truth.
                self.last_cs_digest = Some(d);
            }
        }

        // Wrap encode + solve in catch_unwind as a safety net for any
        // unexpected panics inside the solver (e.g., degree overflow).
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {})); // silence repeated panics
        let cache_enabled = picus_solver::config::with(|c| c.cache_enabled);
        let cache = &mut self.cache;
        // Combine the external cancel (Ctrl-C / parent-process abort)
        // with the per-call timeout into a single token the GB engine
        // polls. Either source fires → GB exits cooperatively. Pre-
        // Phase-5b this only honoured external cancel at entry; the
        // inner solve only saw the timeout.
        let external = cancel.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let timeout_tok = CancelToken::with_timeout(std::time::Duration::from_millis(timeout_ms));
            let cancel = CancelToken::either(&external, &timeout_tok);
            let solve_t0 = if stats_on {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let outcome = if cache_enabled {
                cache.solve(&cs, &cancel)
            } else {
                let enc_t0 = if stats_on {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                let encoded = encode(&cs).map_err(|e| SolverError::Internal(e))?;
                if let Some(t0) = enc_t0 {
                    use std::sync::atomic::Ordering::Relaxed;
                    let dt = t0.elapsed().as_nanos() as u64;
                    let nf = &picus_solver::profile::NATIVE_FF;
                    nf.encode_time_ns.fetch_add(dt, Relaxed);
                    nf.encoded_polys_total
                        .fetch_add(encoded.polynomials.len() as u64, Relaxed);
                    nf.observe_polys_max(encoded.polynomials.len() as u64);
                    nf.observe_vars_max(encoded.poly_ring.n_vars as u64);
                }
                log::debug!(
                    "native-ff: {} polynomials, {} variables",
                    encoded.polynomials.len(),
                    encoded.poly_ring.n_vars
                );
                solve_encoded_with_cancel(&encoded, &cancel)
            };
            if let Some(t0) = solve_t0 {
                use std::sync::atomic::Ordering::Relaxed;
                let dt = t0.elapsed().as_nanos() as u64;
                picus_solver::profile::NATIVE_FF
                    .solve_inner_time_ns
                    .fetch_add(dt, Relaxed);
            }

            match outcome {
                SolveOutcome::Sat(model) => Ok(SolverResult::Sat(model)),
                SolveOutcome::Unsat(_) => Ok(SolverResult::Unsat),
                SolveOutcome::Unknown => Ok(SolverResult::Unknown(UnknownReason::Timeout)),
            }
        }));
        std::panic::set_hook(prev_hook);

        match result {
            Ok(r) => r,
            Err(_) => {
                log::warn!(
                    "native-ff: solver panicked (likely degree overflow); returning Unknown"
                );
                Ok(SolverResult::Unknown(UnknownReason::BackendError(
                    "native-ff solver panicked".into(),
                )))
            }
        }
    }

    fn dump_smt(&self, ir: &PolyIR) -> String {
        let cs = ir_to_constraint_system(ir);
        let mut out = String::new();
        out.push_str(&format!(
            "; Native FF solver (Groebner basis over GF({}))\n",
            cs.prime
        ));
        out.push_str(&format!(
            "; {} equalities, {} assignments\n",
            cs.equalities.len(),
            cs.assignments.len()
        ));
        for (a, b) in &cs.disequalities {
            out.push_str(&format!("; disequality: {} != {}\n", a, b));
        }
        for (i, eq) in cs.equalities.iter().enumerate() {
            out.push_str(&format!("; eq[{}]: ", i));
            for (j, t) in eq.iter().enumerate() {
                if j > 0 {
                    out.push_str(" + ");
                }
                out.push_str(&format!("{}*{}", t.coeff, t.vars.join("*")));
            }
            out.push_str(" = 0\n");
        }
        out
    }
}

inventory::submit! {
    SolverBackendDescriptor {
        name: "native",
        theory: Theory::Ff,
        factory: || Box::new(NativeFfBackend::new()),
    }
}
