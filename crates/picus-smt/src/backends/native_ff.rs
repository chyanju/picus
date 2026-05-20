//! Native Rust finite field solver backend using picus-solver (Groebner basis).
//!
//! This backend is a pure-Rust replacement for cvc5's QF_FF theory solver.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use log;

use crate::query::{UniquenessQuery, IRConstraint, orig_var, alt_var};
use crate::backends::{SolverBackend, SolverResult, SolverError};

use picus_solver::encoder::{ConstraintSystem, PolyTerm, encode};
use picus_solver::core::{solve_encoded_with_cancel, SolveOutcome};
use picus_solver::incremental_context::IncrementalSolverContext;
use picus_solver::timeout::CancelToken;

pub struct NativeFfBackend {
    /// Constraint-side digest of the most recent `solve` call. Used to
    /// count consecutive-same-digest streaks for telemetry.
    last_cs_digest: Option<u64>,
    /// Amortises split-GB across `solve` calls whose constraint side
    /// has not changed. Default-on; disable by setting
    /// `PICUS_NO_INCREMENTAL_CACHE=1`.
    cache: IncrementalSolverContext,
    cache_enabled: bool,
}

impl NativeFfBackend {
    pub fn new() -> Self {
        let cache_enabled = std::env::var_os("PICUS_NO_INCREMENTAL_CACHE").is_none();
        NativeFfBackend {
            last_cs_digest: None,
            cache: IncrementalSolverContext::new(),
            cache_enabled,
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

/// Convert a UniquenessQuery into a ConstraintSystem for picus-solver.
fn query_to_constraint_system(query: &UniquenessQuery) -> ConstraintSystem {
    let prime = query.prime.clone();

    let mut equalities: Vec<Vec<PolyTerm>> = Vec::new();
    let mut assignments: Vec<(String, BigUint)> = Vec::new();

    // x0 = 1 (wire 0 is always the constant 1)
    assignments.push(("x0".into(), BigUint::one()));

    // Named constants (ps1, ps2, ..., zero, one)
    for (name, val) in &query.constants {
        assignments.push((name.clone(), val.clone()));
    }

    // Known signals: x_j = y_j
    // We encode this as: x_j - y_j = 0
    for &j in &query.known_signals {
        if !query.input_indices.contains(&j) {
            // For non-input wires, both x and y exist
            let x_var = orig_var(j);
            let y_var = alt_var(j, false);
            equalities.push(vec![
                PolyTerm { coeff: BigUint::one(), vars: vec![x_var] },
                PolyTerm { coeff: &prime - BigUint::one(), vars: vec![y_var] },
            ]);
        }
    }

    // Convert IR constraints to polynomial terms
    let convert_constraints = |constraints: &[IRConstraint], equalities: &mut Vec<Vec<PolyTerm>>| {
        for c in constraints {
            match c {
                IRConstraint::Linear(terms) => {
                    let poly_terms: Vec<PolyTerm> = terms.iter().map(|t| {
                        PolyTerm { coeff: t.coeff.clone(), vars: vec![t.var.clone()] }
                    }).collect();
                    if !poly_terms.is_empty() {
                        equalities.push(poly_terms);
                    }
                }
                IRConstraint::NonLinear { lhs_terms, rhs_terms } => {
                    // lhs - rhs = 0
                    let mut poly_terms = Vec::new();
                    for t in lhs_terms {
                        poly_terms.push(PolyTerm {
                            coeff: t.coeff.clone(),
                            vars: vec![t.var_a.clone(), t.var_b.clone()],
                        });
                    }
                    // Subtract rhs: negate coefficients
                    for t in rhs_terms {
                        let neg_coeff = if t.coeff.is_zero() {
                            BigUint::zero()
                        } else {
                            &prime - &t.coeff
                        };
                        poly_terms.push(PolyTerm {
                            coeff: neg_coeff,
                            vars: vec![t.var.clone()],
                        });
                    }
                    if !poly_terms.is_empty() {
                        equalities.push(poly_terms);
                    }
                }
                IRConstraint::VarEq(var, val) => {
                    // var = val → encoded as assignment
                    // But we can't add to assignments from here, so encode as polynomial: var - val = 0
                    equalities.push(vec![
                        PolyTerm { coeff: BigUint::one(), vars: vec![var.clone()] },
                        PolyTerm {
                            coeff: if val.is_zero() { BigUint::zero() } else { &prime - val },
                            vars: vec![],
                        },
                    ]);
                }
                IRConstraint::VarNeq(_, _) => {
                    // Disequality is handled separately via the target signal
                }
                IRConstraint::Or(_) => {
                    // Or (disjunction) constraints cannot be soundly encoded
                    // as polynomial equalities. The main Or usage in Picus is
                    // the AB0 optimization, which is disabled for the native
                    // backend. If one appears, skip it and log a warning —
                    // the solver may return Unknown but will not produce a
                    // false UNSAT.
                    log::warn!("Or constraint encountered — skipping (native-ff cannot encode disjunctions)");
                }
            }
        }
    };

    convert_constraints(&query.orig_constraints, &mut equalities);
    convert_constraints(&query.alt_constraints, &mut equalities);

    // Target signal disequality: x_target ≠ y_target
    let target_x = orig_var(query.target_signal);
    let target_y = alt_var(query.target_signal, query.input_indices.contains(&query.target_signal));

    // Filter out zero-coeff terms and empty-vars constant terms that are zero
    let equalities = equalities.into_iter().map(|terms| {
        terms.into_iter().filter(|t| !t.coeff.is_zero()).collect::<Vec<_>>()
    }).filter(|terms: &Vec<PolyTerm>| !terms.is_empty()).collect();

    ConstraintSystem {
        prime,
        equalities,
        disequalities: vec![(target_x, target_y)],
        assignments,
        add_field_polys: false, // BN128 prime is too large for field polys
        bitsums: vec![],
    }
}

impl SolverBackend for NativeFfBackend {
    fn solve(
        &mut self,
        query: &UniquenessQuery,
        timeout_ms: u64,
    ) -> Result<SolverResult, SolverError> {
        let cs = query_to_constraint_system(query);
        let stats_on = picus_solver::profile::gb_stats_enabled();
        let cs_digest = if stats_on { Some(digest_constraint_side(&cs)) } else { None };
        if stats_on {
            use std::sync::atomic::Ordering::Relaxed;
            let nf = &picus_solver::profile::NATIVE_FF;
            nf.solve_calls.fetch_add(1, Relaxed);
            if let Some(d) = cs_digest {
                if self.last_cs_digest == Some(d) {
                    nf.repeated_cs_digest_streak.fetch_add(1, Relaxed);
                }
                // Note: distinct_cs_digests counter is incremented inside
                // `IncrementalSolverContext::solve` on rebuild — keeping a
                // single source of truth.
                self.last_cs_digest = Some(d);
            }
        }

        // Wrap encode + solve in catch_unwind as a safety net for any
        // unexpected panics inside the solver (e.g., degree overflow).
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {})); // silence repeated panics
        let cache_enabled = self.cache_enabled;
        let cache = &mut self.cache;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let cancel = CancelToken::with_timeout(std::time::Duration::from_millis(timeout_ms));
            let solve_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
            let outcome = if cache_enabled {
                // Cached path. Encoding is amortised inside the cache
                // (re-encodes only on miss); per-query work is the
                // Rabinowitsch polynomial plus an incremental GB
                // extend.
                cache.solve(&cs, &cancel)
            } else {
                // Stateless path, selected by
                // `PICUS_NO_INCREMENTAL_CACHE=1`.
                let enc_t0 = if stats_on { Some(std::time::Instant::now()) } else { None };
                let encoded = encode(&cs).map_err(|e| SolverError::Internal(e))?;
                if let Some(t0) = enc_t0 {
                    use std::sync::atomic::Ordering::Relaxed;
                    let dt = t0.elapsed().as_nanos() as u64;
                    let nf = &picus_solver::profile::NATIVE_FF;
                    nf.encode_time_ns.fetch_add(dt, Relaxed);
                    nf.encoded_polys_total.fetch_add(encoded.polynomials.len() as u64, Relaxed);
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
                picus_solver::profile::NATIVE_FF.solve_inner_time_ns.fetch_add(dt, Relaxed);
            }

            match outcome {
                SolveOutcome::Sat(model) => Ok(SolverResult::Sat(model)),
                SolveOutcome::Unsat(_) => Ok(SolverResult::Unsat),
                SolveOutcome::Unknown => Ok(SolverResult::Unknown),
            }
        }));
        std::panic::set_hook(prev_hook); // restore hook

        match result {
            Ok(r) => r,
            Err(_) => {
                log::warn!("native-ff: solver panicked (likely degree overflow); returning Unknown");
                Ok(SolverResult::Unknown)
            }
        }
    }

    fn dump_smt(&self, query: &UniquenessQuery) -> String {
        // Generate a human-readable representation of the polynomial system
        let cs = query_to_constraint_system(query);
        let mut out = String::new();
        out.push_str(&format!("; Native FF solver (Groebner basis over GF({}))\n", cs.prime));
        out.push_str(&format!("; {} equalities, {} assignments\n",
            cs.equalities.len(), cs.assignments.len()));
        for (a, b) in &cs.disequalities {
            out.push_str(&format!("; disequality: {} != {}\n", a, b));
        }
        for (i, eq) in cs.equalities.iter().enumerate() {
            out.push_str(&format!("; eq[{}]: ", i));
            for (j, t) in eq.iter().enumerate() {
                if j > 0 { out.push_str(" + "); }
                out.push_str(&format!("{}*{}", t.coeff, t.vars.join("*")));
            }
            out.push_str(" = 0\n");
        }
        out
    }
}
