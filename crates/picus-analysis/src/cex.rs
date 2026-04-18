//! Counterexample generation (stub).

use crate::dpvl::DpvlResult;

/// Scope-by-scope counterexample construction.
/// Currently a stub — the main DPVL flow handles the common case.
pub fn run_cex(
    _r1cs: &picus_r1cs::grammar::R1csFile,
    _config: &crate::dpvl::DpvlConfig,
) -> DpvlResult {
    DpvlResult::Unknown
}
