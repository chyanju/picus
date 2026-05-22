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
use picus_solver::encoder::{encode, ConstraintSystem, PolyTerm};
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
/// [`picus_solver::incremental_context::digest_constraint_side`]. The
/// cache itself uses the same function for its hit/miss decisions, so
/// the digests agree.
fn digest_constraint_side(cs: &ConstraintSystem) -> u64 {
    picus_solver::incremental_context::digest_constraint_side(cs)
}

/// Lower a `PolyIR` to the `ConstraintSystem` shape consumed by
/// [`picus_solver::core::solve_encoded_with_cancel`]. Each polynomial
/// equality becomes one `Vec<PolyTerm>` summing to zero; the target
/// disequality lifts to the solver's `disequalities` slot.
fn ir_to_constraint_system(ir: &PolyIR) -> ConstraintSystem {
    let prime = ir.ring.field.prime().clone();

    let mut equalities: Vec<Vec<PolyTerm>> = Vec::with_capacity(ir.equalities.len());
    for poly in &ir.equalities {
        let terms: Vec<PolyTerm> = ir
            .poly_terms(poly)
            .filter(|(coeff, _)| !coeff_is_zero(coeff))
            .map(|(coeff, vars)| PolyTerm { coeff, vars })
            .collect();
        if !terms.is_empty() {
            equalities.push(terms);
        }
    }

    // Field polynomials `x^p - x = 0` are essential for sound GB
    // reasoning over small primes (otherwise the GB engine treats `x`
    // as ranging over the algebraic closure, not GF(p)), but are
    // prohibitively expensive for cryptographic primes. The encoder
    // refuses to materialise them past `prime > 1000` anyway, so just
    // mirror its gate here.
    let small_prime_threshold = num_bigint::BigUint::from(1000u32);
    let add_field_polys = prime <= small_prime_threshold;
    ConstraintSystem {
        prime,
        equalities,
        disequalities: vec![(
            ir.x_name(ir.target_signal).to_string(),
            ir.y_name(ir.target_signal).to_string(),
        )],
        // PolyIR bakes `x_0 = 1` and the input equalities `x_i = y_i`
        // straight into `equalities`, so no explicit assignments are
        // required by the encoder.
        assignments: Vec::new(),
        add_field_polys,
        bitsums: vec![],
    }
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
        // Honour external cancellation at entry. Mid-solve external
        // cancel would require combining the caller's token with the
        // internal `with_timeout` token; deferred to phase 5.
        if cancel.is_cancelled() {
            return Ok(SolverResult::Unknown(UnknownReason::Timeout));
        }
        let cs = ir_to_constraint_system(ir);
        let stats_on = picus_solver::profile::gb_stats_enabled();
        let cs_digest = if stats_on {
            Some(digest_constraint_side(&cs))
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
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let cancel = CancelToken::with_timeout(std::time::Duration::from_millis(timeout_ms));
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
