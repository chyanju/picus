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

use std::cell::Cell;
use std::sync::Once;

use picus_solver::core::{solve_encoded_with_cancel, SolveOutcome};
use picus_solver::frontend::encoder::ConstraintSystem;
use picus_solver::incremental_context::IncrementalSolverContext;
use picus_core::timeout::CancelToken;
use picus_core::metric;
use picus_core::profile::NATIVE_FF;

thread_local! {
    /// When true on the current thread, the installed panic hook stays
    /// silent. Set only while a solve's `catch_unwind` is active, so an
    /// expected solver panic (e.g. degree overflow) does not spam stderr
    /// — without globally muting panics on other threads or outside a solve.
    static SILENCE_SOLVER_PANIC: Cell<bool> = const { Cell::new(false) };
}

static HOOK_INIT: Once = Once::new();

/// Install, once per process, a panic hook that delegates to the
/// previous hook except on threads currently inside a solver
/// `catch_unwind` (see [`SILENCE_SOLVER_PANIC`]). Avoids swapping the
/// process-global hook on every `solve` call, which races under
/// multi-threaded use and can suppress an embedder's hook.
fn install_silencing_hook() {
    HOOK_INIT.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SILENCE_SOLVER_PANIC.with(|c| c.get()) {
                prev(info);
            }
        }));
    });
}

/// RAII guard: sets the thread-local silence flag and restores its
/// prior value on drop (including on unwind).
struct PanicSilenceGuard(bool);

impl PanicSilenceGuard {
    fn new() -> Self {
        install_silencing_hook();
        let prev = SILENCE_SOLVER_PANIC.with(|c| c.replace(true));
        PanicSilenceGuard(prev)
    }
}

impl Drop for PanicSilenceGuard {
    fn drop(&mut self) {
        let prev = self.0;
        SILENCE_SOLVER_PANIC.with(|c| c.set(prev));
    }
}

pub struct NativeFfBackend {
    /// Constraint-side digest of the most recent `solve` call. Used to
    /// count consecutive-same-digest streaks for telemetry.
    last_cs_digest: Option<u128>,
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
/// Used by the repeat-detection telemetry to update `last_cs_digest`.
fn digest_native_constraint_side(ics: &ConstraintSystem) -> u128 {
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
        // Opt-in linear (Gaussian) pre-elimination (off by default; see
        // `RuntimeConfig::linear_elim`). When enabled, reduce the equality
        // system once here so both the conjunctive and CDCL(T) per-check
        // paths see the eliminated generators.
        let reduced_ir = if picus_core::config::with(|c| c.linear_elim) {
            ir.pre_eliminate_linear(cancel)
        } else {
            None
        };
        let ir: &PolyIR = reduced_ir.as_ref().unwrap_or(ir);
        let indexed = ir.to_constraint_system();
        metric::incr!(NATIVE_FF.solve_calls);
        metric::scope! {
            // Repeat-detection over consecutive constraint sides. The digest
            // is expensive and the streak counter needs persisted
            // last-digest state, both of which belong inside the gated
            // `metric::scope!` so neither runs when profiling is off.
            let d = digest_native_constraint_side(&indexed);
            if self.last_cs_digest == Some(d) {
                metric::incr!(NATIVE_FF.repeated_cs_digest_streak);
            }
            // `distinct_cs_digests` is incremented inside
            // `IncrementalSolverContext::solve` on rebuild — single source of truth.
            self.last_cs_digest = Some(d);
        }

        // Wrap encode + solve in catch_unwind as a safety net for any
        // unexpected panics inside the solver (e.g., degree overflow).
        // The guard silences the (expected) panic message on this thread
        // for the duration; the process-global hook is installed once.
        let silence_guard = PanicSilenceGuard::new();
        let cache_enabled = picus_core::config::with(|c| c.cache_enabled);
        let cache = &mut self.cache;
        // Combine the external cancel (Ctrl-C / parent-process abort)
        // with the per-call timeout into a single token the GB engine
        // polls. Either source fires → GB exits cooperatively.
        let external = cancel.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let timeout_tok = CancelToken::with_timeout(std::time::Duration::from_millis(timeout_ms));
            let cancel = CancelToken::either(&external, &timeout_tok);
            metric::timer!(NATIVE_FF.solve_inner_time_ns);
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
                // Stateless path: encode directly via `PolyIR::encode`.
                let encoded = {
                    metric::timer!(NATIVE_FF.encode_time_ns);
                    ir.encode().map_err(|e| SolverError::Internal(e))?
                };
                metric::add!(NATIVE_FF.encoded_polys_total, encoded.polynomials.len() as u64);
                metric::max!(NATIVE_FF.encoded_polys_max, encoded.polynomials.len() as u64);
                metric::max!(NATIVE_FF.encoded_vars_max, encoded.poly_ring.n_vars() as u64);
                log::debug!(
                    "native-ff: {} polynomials, {} variables",
                    encoded.polynomials.len(),
                    encoded.poly_ring.n_vars()
                );
                solve_encoded_with_cancel(&encoded, &cancel)
            };
            match outcome {
                SolveOutcome::Sat(model) => Ok(SolverResult::Sat(model)),
                SolveOutcome::Unsat(_) => Ok(SolverResult::Unsat),
                SolveOutcome::Unknown => Ok(SolverResult::Unknown(UnknownReason::Timeout)),
            }
        }));
        drop(silence_guard);

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
