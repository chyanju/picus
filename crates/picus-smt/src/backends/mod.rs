//! Solver backend trait and common types.
//!
//! The cvc5 and z3 backends are opt-in Cargo features (default off): the
//! default `native` build skips their expensive vendored compiles. Enable
//! them with `--features cvc5` / `--features z3`.

#[cfg(feature = "cvc5")]
pub mod cvc5_ff;
#[cfg(feature = "cvc5")]
pub mod cvc5_nia;
pub mod native_ff;
/// Native-engine lowering methods on `PolyIR` (kept off the
/// solver-agnostic IR so `poly_ir` depends only on picus-core).
mod native_lower;
#[cfg(feature = "z3")]
pub mod z3_nia;

use num_bigint::BigUint;
use std::collections::HashMap;
use thiserror::Error;

use crate::poly_ir::PolyIR;
use picus_core::timeout::CancelToken;

/// Why a solver could not commit to `Sat` or `Unsat`. Discriminating
/// these lets callers retry with a longer budget (`Timeout`),
/// downgrade the verdict (`IncompleteTheory`), or surface a hard
/// failure to the user (`BackendError`).
#[derive(Debug, Clone)]
pub enum UnknownReason {
    /// The budget (wall-clock timeout or cancel token) fired before
    /// the solver finished.
    Timeout,
    /// The solver's theory can't decide this query (e.g. cvc5 QF_FF
    /// returning `unknown` on an `or` clause it doesn't currently
    /// handle, or a GB engine missing field polys for a small prime).
    IncompleteTheory,
    /// Internal solver failure: panic recovery, process crash,
    /// malformed model, etc. The string carries the original message
    /// for logs / debugging.
    BackendError(String),
}

/// Result from a solver invocation.
#[derive(Debug, Clone)]
pub enum SolverResult {
    Unsat,
    Sat(HashMap<String, BigUint>),
    Unknown(UnknownReason),
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("solver error: {0}")]
    Internal(String),
    #[error("unsupported solver/theory combination: {0}")]
    Unsupported(String),
}

/// Trait for solver backends.
///
/// Backends consume a [`PolyIR`] snapshot whose `target_signal` and
/// `known_signals` reflect the current DPVL state. The PolyIR's
/// `equalities` already encode `x_0 = 1` and every learned equality from
/// previous solves (input wires reuse `x_i` across copies, so no
/// `x_i = y_i` equality appears); the
/// backend additionally asserts `x_target ≠ y_target` and runs SMT
/// `(check-sat)`. SAT models are returned as
/// `HashMap<String, BigUint>` keyed by the ring's canonical variable
/// names (`x0`, `y3`, ...).
pub trait SolverBackend {
    /// Run the SMT query encoded by `ir`. The backend honours **both**
    /// `timeout_ms` (its own per-call budget) and `cancel` (an external
    /// cancellation channel, e.g. Ctrl-C reaching the analyser). Either
    /// firing should land in `SolverResult::Unknown(UnknownReason::Timeout)`.
    /// Backends that only support one of the two should document that
    /// limitation rather than silently ignoring the other.
    fn solve(
        &mut self,
        ir: &PolyIR,
        timeout_ms: u64,
        cancel: &CancelToken,
    ) -> Result<SolverResult, SolverError>;

    fn dump_smt(&self, ir: &PolyIR) -> String;
}

/// Factory closure constructing a fresh backend instance.
pub type BackendFactory = fn() -> Box<dyn SolverBackend>;

/// Inventory entry for an SMT backend.
///
/// Backends register themselves with `inventory::submit!` from their
/// own module; [`create_backend_by_name`] walks the registry at
/// *dispatch* time, and [`crate::SolverKind::from_str`] consults it to
/// list the known backends in its error message. *Selection by name*,
/// however, goes through the built-in [`crate::SolverKind`] enum (used
/// by `--solver` and config files), so a new backend that should be
/// reachable via `--solver` also needs a matching `SolverKind` variant
/// and `from_str` arm. A backend registered only via `inventory::submit!`
/// is dispatchable through `create_backend_by_name` directly but is not
/// selectable by name. The built-in `SolverKind` `name` values are the
/// lowercase strings here.
pub struct SolverBackendDescriptor {
    /// Stable name used by `--solver`, `SolverKind::from_str`, and
    /// `dump_smt` log lines.
    pub name: &'static str,
    /// Theory this backend serves. `create_backend` filters by
    /// `(name, theory)`.
    pub theory: crate::Theory,
    /// Factory closure constructing a fresh backend instance.
    pub factory: BackendFactory,
}

inventory::collect!(SolverBackendDescriptor);

/// Iterate every backend descriptor registered via `inventory`.
/// Stable order by `(name, theory)` for reproducible dispatch.
pub fn all_backend_descriptors() -> Vec<&'static SolverBackendDescriptor> {
    let mut v: Vec<&SolverBackendDescriptor> =
        inventory::iter::<SolverBackendDescriptor>.into_iter().collect();
    v.sort_by_key(|d| (d.name, theory_key(d.theory)));
    v
}

fn theory_key(t: crate::Theory) -> u8 {
    match t {
        crate::Theory::Ff => 0,
        crate::Theory::Nia => 1,
    }
}

/// Look up a backend by `(name, theory)`. Returns the factory's
/// freshly-built instance, or `None` if no descriptor matches.
pub fn create_backend_by_name(
    name: &str,
    theory: crate::Theory,
) -> Option<Box<dyn SolverBackend>> {
    all_backend_descriptors()
        .into_iter()
        .find(|d| d.name == name && d.theory == theory)
        .map(|d| (d.factory)())
}

// ─── Shared SMT-LIB-text helpers (NIA backends) ────────────────────

/// Emit a single `Poly` as an SMT-LIB nonlinear-integer-arithmetic
/// expression. Each `(coeff, monomial_vars)` term becomes
/// `(* coeff v1 v2 ...)`; the sum is wrapped in `(+ ...)` when it has
/// more than one term, and an empty polynomial reduces to literal `0`.
#[cfg(any(feature = "cvc5", feature = "z3"))]
pub fn poly_to_smtlib_nia(ir: &PolyIR, poly: &picus_core::poly::IrPoly) -> String {
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![coeff.to_string()];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(* {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => "0".to_string(),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(+ {})", parts.join(" ")),
    }
}

/// Emit a single `Poly` as an SMT-LIB QF_FF expression, using
/// `ff.add` / `ff.mul` and `#fNmP` literals over the field defined
/// by the ring's prime.
#[cfg(feature = "cvc5")]
pub fn poly_to_smtlib_ff(ir: &PolyIR, poly: &picus_core::poly::IrPoly) -> String {
    let p = ir.ring.field().prime();
    let parts: Vec<String> = ir
        .poly_terms(poly)
        .map(|(coeff, vars)| {
            let mut atoms = vec![format!("#f{}m{}", coeff, p)];
            atoms.extend(vars);
            if atoms.len() == 1 {
                atoms.pop().unwrap()
            } else {
                format!("(ff.mul {})", atoms.join(" "))
            }
        })
        .collect();
    match parts.len() {
        0 => format!("#f0m{}", p),
        1 => parts.into_iter().next().unwrap(),
        _ => format!("(ff.add {})", parts.join(" ")),
    }
}

#[cfg(test)]
mod tests;
