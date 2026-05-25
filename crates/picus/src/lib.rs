//! Picus — automated detection of under-constrained signals in ZK circuits.
//!
//! This crate provides both high-level convenience functions and access to
//! the underlying analysis components.
//!
//! # Quick Start
//!
//! ```no_run
//! use picus::{check_circuit, Config, CheckResult};
//!
//! let result = check_circuit("circuit.r1cs", Config::default()).unwrap();
//! match result {
//!     CheckResult::Safe => println!("All output signals are uniquely determined"),
//!     CheckResult::Unsafe { witness_1, witness_2 } => {
//!         println!("Found two distinct witnesses with the same inputs");
//!     }
//!     CheckResult::Unknown => println!("Could not determine uniqueness"),
//! }
//! ```

use std::collections::{HashMap, HashSet};
use std::path::Path;

// ============================================================
// Re-exports — users only need `use picus::*`
// ============================================================

/// Big unsigned integer type used for field element values.
pub use num_bigint::BigUint;

/// R1CS file representation.
pub use picus_r1cs::grammar::R1csFile;

/// R1CS parsing error.
pub use picus_r1cs::parser::R1csParseError;

/// Read an R1CS binary file from a file path.
pub use picus_r1cs::parser::read_r1cs_file;

/// Read an R1CS binary from a byte slice.
pub use picus_r1cs::parser::read_r1cs;

/// Solver backend selection.
pub use picus_smt::SolverKind;

/// SMT theory selection.
pub use picus_smt::Theory;

/// Propagation lemma set configuration.
pub use picus_analysis::dpvl::LemmaSet;

/// Signal selection strategy.
pub use picus_analysis::selector::SelectorKind;

/// Groebner basis algorithm strategy used by the native FF backend.
pub use picus_solver::config::GbStrategy;

// Sub-crates exposed for advanced usage (e.g., dump_smt, custom pipelines).
pub use picus_r1cs;
pub use picus_smt;
pub use picus_analysis;
pub use picus_solver;

// ============================================================
// Error type
// ============================================================

/// Errors that can occur during Picus analysis.
#[derive(Debug, thiserror::Error)]
pub enum PicusError {
    /// Failed to parse the R1CS binary file.
    #[error("R1CS parse error: {0}")]
    Parse(#[from] R1csParseError),

    /// Solver returned an error or failed to initialize.
    #[error("solver error: {0}")]
    Solver(String),

    /// Invalid solver/theory combination or other configuration issue.
    #[error("invalid configuration: {0}")]
    Config(String),

    /// File I/O error.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

// ============================================================
// Configuration
// ============================================================

/// Analysis configuration with sensible defaults.
///
/// Default: `cvc5` solver, `ff` theory, all lemmas enabled, 5000ms timeout.
#[derive(Debug, Clone)]
pub struct Config {
    /// Solver backend. Default: `SolverKind::Cvc5`.
    pub solver: SolverKind,
    /// SMT theory. Default: `Theory::Ff`.
    pub theory: Theory,
    /// Per-query solver timeout in milliseconds. Default: 5000.
    pub timeout_ms: u64,
    /// Propagation lemmas to enable. Default: all.
    pub lemmas: LemmaSet,
    /// Signal selection strategy. Default: `SelectorKind::Counter`.
    pub selector: SelectorKind,
    /// If set, dump each SMT query to this directory for debugging.
    pub dump_smt: Option<std::path::PathBuf>,
    /// Groebner basis algorithm strategy (native FF backend only).
    /// Default: `GbStrategy::Direct`.
    pub gb_strategy: GbStrategy,
    /// Emit per-site wall-clock profile data to stderr at process exit.
    /// Default: `false`.
    pub profile: bool,
    /// Emit per-run GB statistics to stderr. Default: `false`.
    pub gb_stats: bool,
    /// Use F4 matrix reduction for batched same-sugar S-pairs (native
    /// FF backend only). Default: `false`.
    pub use_f4: bool,
    /// Pick DNF instead of CNF for the boolean layer (native FF
    /// backend only). Default: `false`.
    pub dnf_enabled: bool,
    /// DNF expansion cap; native FF returns `Unknown` beyond this
    /// disjunct count. Default: `100_000`.
    pub dnf_cap: u64,
    /// CDCL(T) outer-iteration cap; `0` forces immediate `Unknown`
    /// (test helper), `u64::MAX` for effectively unbounded.
    /// Default: `1_000_000`.
    pub cdclt_iter_cap: u64,
    /// Emit GB trace events for the in-flight basis to stderr.
    /// Default: `false`.
    pub gb_trace: bool,
    /// Reuse the incremental Buchberger cache between native FF
    /// `solve()` calls. Default: `true`.
    pub cache_enabled: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            solver: SolverKind::Cvc5,
            theory: Theory::Ff,
            timeout_ms: 5000,
            lemmas: LemmaSet::all(),
            selector: SelectorKind::Counter,
            dump_smt: None,
            gb_strategy: GbStrategy::Direct,
            profile: false,
            gb_stats: false,
            use_f4: false,
            dnf_enabled: false,
            dnf_cap: 100_000,
            cdclt_iter_cap: 1_000_000,
            gb_trace: false,
            cache_enabled: true,
        }
    }
}

// ============================================================
// Result type
// ============================================================

/// Result of a uniqueness check.
#[derive(Debug, Clone)]
pub enum CheckResult {
    /// All output signals are uniquely determined by the inputs.
    Safe,

    /// Found two distinct valid witnesses sharing the same inputs.
    /// The witnesses differ on at least one output signal.
    Unsafe {
        /// Original witness values: signal name → field element value.
        /// Only contains circuit signals (x0, x1, ...), not internal constants.
        witness_1: HashMap<String, BigUint>,
        /// Alternative witness values: signal name → field element value.
        /// Only contains circuit signals (y1, y2, ...), not internal constants.
        witness_2: HashMap<String, BigUint>,
    },

    /// The analysis could not determine uniqueness within the timeout.
    Unknown,
}

// ============================================================
// High-level API
// ============================================================

/// Check uniqueness of output signals in an R1CS circuit from a file path.
///
/// This is the main entry point for programmatic use. It reads the R1CS file,
/// configures the solver and propagation lemmas, runs the DPVL algorithm,
/// and returns a structured result.
///
/// # Example
///
/// ```no_run
/// use picus::{check_circuit, Config};
///
/// let result = check_circuit("circuit.r1cs", Config::default()).unwrap();
/// println!("{:?}", result);
/// ```
pub fn check_circuit(
    path: impl AsRef<Path>,
    config: Config,
) -> Result<CheckResult, PicusError> {
    let r1cs = picus_r1cs::parser::read_r1cs_file(path.as_ref())?;
    check_r1cs(&r1cs, config)
}

/// Check uniqueness of output signals from raw R1CS bytes.
///
/// # Example
///
/// ```no_run
/// use picus::{check_r1cs_bytes, Config};
///
/// let data = std::fs::read("circuit.r1cs").unwrap();
/// let result = check_r1cs_bytes(&data, Config::default()).unwrap();
/// ```
pub fn check_r1cs_bytes(
    data: &[u8],
    config: Config,
) -> Result<CheckResult, PicusError> {
    let r1cs = picus_r1cs::parser::read_r1cs(data)?;
    check_r1cs(&r1cs, config)
}

/// Check uniqueness on a pre-parsed R1csFile.
///
/// Useful when you want to inspect the R1CS structure before running the analysis,
/// or when running multiple analyses on the same circuit with different configs.
pub fn check_r1cs(
    r1cs: &R1csFile,
    config: Config,
) -> Result<CheckResult, PicusError> {
    // Validate solver/theory combination
    picus_smt::validate_combination(config.solver, config.theory)
        .map_err(PicusError::Config)?;

    // Create dump directory if needed
    if let Some(ref dir) = config.dump_smt {
        let _ = std::fs::create_dir_all(dir);
    }

    // Apply runtime config to the current thread. ConfigGuard restores
    // the prior settings when this function returns, so concurrent
    // callers on other threads are unaffected and overlapping calls on
    // the same thread can't leak settings into siblings.
    let _solver_cfg = picus_solver::config::ConfigGuard::with_override(|c| {
        c.gb_strategy = config.gb_strategy;
        c.profile_enabled = config.profile;
        c.gb_stats_enabled = config.gb_stats;
        c.use_f4 = config.use_f4;
        c.dnf_enabled = config.dnf_enabled;
        c.dnf_cap = config.dnf_cap;
        c.cdclt_iter_cap = config.cdclt_iter_cap;
        c.gb_trace_enabled = config.gb_trace;
        c.cache_enabled = config.cache_enabled;
    });

    // Build internal DPVL config
    let dpvl_config = picus_analysis::dpvl::DpvlConfig {
        solver: config.solver,
        theory: config.theory,
        selector: config.selector,
        timeout_ms: config.timeout_ms,
        lemmas: config.lemmas,
        dump_smt: config.dump_smt,
    };

    // Run DPVL
    let result = picus_analysis::dpvl::run_dpvl(r1cs, &dpvl_config)
        .map_err(PicusError::Solver)?;

    // Convert internal result to public API result
    match result {
        picus_analysis::dpvl::DpvlResult::Safe => Ok(CheckResult::Safe),
        picus_analysis::dpvl::DpvlResult::Unsafe(model) => {
            let (w1, w2) = split_model(&model);
            Ok(CheckResult::Unsafe {
                witness_1: w1,
                witness_2: w2,
            })
        }
        picus_analysis::dpvl::DpvlResult::Unknown => Ok(CheckResult::Unknown),
    }
}

// ============================================================
// Internal helpers
// ============================================================

// ============================================================
// Profile / stats dumps
// ============================================================

/// Write the accumulated per-site wall-clock profile to stderr (if
/// `Config::profile` was set during a previous `check_r1cs` call).
/// `tag` is a free-form label printed alongside the table.
pub fn dump_profile(tag: &str) {
    picus_solver::profile::dump_to_stderr(tag);
}

/// Write the accumulated split-GB / DFS counters to stderr (if
/// `Config::gb_stats` was set during a previous `check_r1cs` call).
pub fn dump_gb_stats() {
    picus_solver::profile::dump_split_stats_to_stderr();
}

// ============================================================
// Internal helpers
// ============================================================

/// Split a raw solver model into two clean witness maps, filtering
/// out internal constants (ps1, zero, etc.). Routing is by the
/// PolyIR convention: keys matching `x<digits>` go to witness 1, keys
/// matching `y<digits>` to witness 2. Anything else (an aux var the
/// solver invented, a Rabinowitsch witness, ...) is treated as
/// witness 1 by default rather than misclassified by prefix.
fn split_model(
    model: &HashMap<String, BigUint>,
) -> (HashMap<String, BigUint>, HashMap<String, BigUint>) {
    let constants: HashSet<&str> = picus_smt::SUBP_CONSTANT_NAMES.iter().copied().collect();

    let mut w1 = HashMap::new();
    let mut w2 = HashMap::new();

    for (var, val) in model {
        if constants.contains(var.as_str()) {
            continue;
        }
        let is_alt_copy = var.starts_with('y')
            && picus_r1cs::parse_var_index(var).is_some();
        if is_alt_copy {
            w2.insert(var.clone(), val.clone());
        } else {
            w1.insert(var.clone(), val.clone());
        }
    }

    (w1, w2)
}
