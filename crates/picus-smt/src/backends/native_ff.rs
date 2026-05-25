//! Native Rust finite-field solver backend — a pure-Rust replacement
//! for the cvc5 QF_FF theory solver.
//!
//! Consumes a [`PolyIR`] snapshot directly: `PolyIR::to_constraint_system`
//! lowers it to the canonical index-keyed
//! `picus_solver::frontend::encoder::ConstraintSystem` (each equality a
//! `Vec<PolyTerm>` summed to zero), and the target disequality
//! `x_target ≠ y_target` is handed to the GB solver via the
//! Rabinowitsch trick wired into [`IncrementalSolverContext`].

use crate::backends::{SolverBackend, SolverBackendDescriptor, SolverError, SolverResult, UnknownReason};
use crate::poly_ir::PolyIR;
use crate::Theory;

use picus_solver::core::{solve_encoded_with_cancel, SolveOutcome};
use picus_solver::frontend::encoder::ConstraintSystem;
use picus_solver::incremental_context::IncrementalSolverContext;
use picus_core::timeout::CancelToken;

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

/// Thin wrapper around the cache module's `digest_constraint_side`.
/// Used for the stats path's `last_cs_digest` tracking.
fn digest_native_constraint_side(ics: &ConstraintSystem) -> u64 {
    picus_solver::incremental_context::digest_constraint_side(ics)
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
        let indexed = ir.to_constraint_system();
        let stats_on = picus_core::profile::gb_stats_enabled();
        let cs_digest = if stats_on {
            Some(digest_native_constraint_side(&indexed))
        } else {
            None
        };
        if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            let nf = &picus_core::profile::NATIVE_FF;
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
        let cache_enabled = picus_core::config::with(|c| c.cache_enabled);
        let cache = &mut self.cache;
        // Combine the external cancel (Ctrl-C / parent-process abort)
        // with the per-call timeout into a single token the GB engine
        // polls. Either source fires → GB exits cooperatively.
        let external = cancel.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let timeout_tok = CancelToken::with_timeout(std::time::Duration::from_millis(timeout_ms));
            let cancel = CancelToken::either(&external, &timeout_tok);
            let solve_t0 = if stats_on {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let outcome = if !ir.disjunctions.is_empty() {
                // Disjunction-aware path: route the whole query
                // (conjunctive constraints + `or` clauses + target
                // diseq) through the in-tree CDCL(T) engine. Each theory
                // check re-validates its model via `verify_model`, so
                // this path has the same spurious-SAT immunity as the
                // plain GB path below. Non-asserting theory conflicts are
                // resolved via 1-UIP and `analyze` bails gracefully
                // rather than panicking; the outer `catch_unwind` remains
                // the ultimate never-panic guard.
                log::debug!(
                    "native-ff: {} disjunction(s) → CDCL(T) path",
                    ir.disjunctions.len()
                );
                let query = ir.to_boolean_query();
                picus_solver::boolean::solve_boolean_query(&query, &cancel)
            } else if cache_enabled {
                cache.solve(&indexed, &cancel)
            } else {
                let enc_t0 = if stats_on {
                    Some(std::time::Instant::now())
                } else {
                    None
                };
                // Stateless path: encode directly via `PolyIR::encode`.
                let encoded = ir.encode().map_err(|e| SolverError::Internal(e))?;
                if let Some(t0) = enc_t0 {
                    use std::sync::atomic::Ordering::Relaxed;
                    let dt = t0.elapsed().as_nanos() as u64;
                    let nf = &picus_core::profile::NATIVE_FF;
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
                picus_core::profile::NATIVE_FF
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
        let ics = ir.to_constraint_system();
        let resolve = |idx: u32| ics.var_names[idx as usize].as_str();
        let mut out = String::new();
        out.push_str(&format!(
            "; Native FF solver (Groebner basis over GF({}))\n",
            ics.prime
        ));
        out.push_str(&format!(
            "; {} equalities, {} assignments\n",
            ics.equalities.len(),
            ics.assignments.len()
        ));
        for &(a, b) in &ics.disequalities {
            out.push_str(&format!(
                "; disequality: {} != {}\n",
                resolve(a),
                resolve(b)
            ));
        }
        for (i, eq) in ics.equalities.iter().enumerate() {
            out.push_str(&format!("; eq[{}]: ", i));
            for (j, t) in eq.iter().enumerate() {
                if j > 0 {
                    out.push_str(" + ");
                }
                let vars_text: String = t
                    .vars
                    .iter()
                    .map(|&(idx, exp)| {
                        let name = resolve(idx);
                        std::iter::repeat(name)
                            .take(exp as usize)
                            .collect::<Vec<_>>()
                            .join("*")
                    })
                    .collect::<Vec<_>>()
                    .join("*");
                out.push_str(&format!("{}*{}", t.coeff, vars_text));
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
