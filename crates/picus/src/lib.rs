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

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

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
pub use picus_core::config::GbStrategy;

/// Polynomial storage representation for the native FF backend.
pub use picus_core::config::ReprKind;

/// Analysis-layer config (solver, theory, lemmas, selector, …): the
/// `analysis` half of [`PicusConfig`].
pub use picus_analysis::dpvl::DpvlConfig as AnalysisConfig;

/// Engine-layer config (GB strategy, representation, caps, …): the
/// `engine` half of [`PicusConfig`].
pub use picus_core::config::RuntimeConfig as EngineConfig;

/// Partial overlay (all fields optional) for the analysis layer.
pub use picus_analysis::dpvl::DpvlOverlay as AnalysisOverlay;

/// Partial overlay (all fields optional) for the engine layer.
pub use picus_core::config::EngineOverlay;

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

/// The fully-resolved Picus configuration.
///
/// Two layers, each its own struct so a knob is declared exactly once:
/// * [`analysis`](PicusConfig::analysis) — solver, theory, lemmas,
///   selector, timeout, SMT dump dir.
/// * [`engine`](PicusConfig::engine) — native-FF-backend knobs: GB
///   strategy, polynomial representation, caps, diagnostics.
///
/// `PicusConfig::default()` is the compiled-in default (zero I/O — what
/// a library import gets with no config). The CLI builds its config by
/// layering, in increasing precedence: defaults → config file → CLI
/// flags (see [`resolve_config`]).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct PicusConfig {
    /// Analysis-layer configuration.
    pub analysis: AnalysisConfig,
    /// Engine-layer (native FF backend) configuration.
    pub engine: EngineConfig,
}

/// Backwards-compatible alias for [`PicusConfig`].
pub type Config = PicusConfig;

/// Partial overlay for [`PicusConfig`]: every field optional. One
/// config source (file, environment, CLI) builds an overlay carrying
/// only the knobs it sets, then merges it onto a base via
/// [`PicusConfig::apply_overlay`]. The TOML form is two optional tables:
///
/// ```toml
/// [analysis]
/// solver = "cvc5"
/// [engine]
/// poly_repr = "sparse"
/// ```
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct PicusConfigOverlay {
    pub analysis: AnalysisOverlay,
    pub engine: EngineOverlay,
}

impl PicusConfig {
    /// Merge an overlay (one config layer) onto this config; only the
    /// overlay's `Some` fields override. A bad enum string in the
    /// analysis layer surfaces as [`PicusError::Config`].
    pub fn apply_overlay(&mut self, o: &PicusConfigOverlay) -> Result<(), PicusError> {
        self.analysis
            .apply_overlay(&o.analysis)
            .map_err(PicusError::Config)?;
        self.engine.apply_overlay(&o.engine);
        Ok(())
    }

    /// Parse a TOML document into a [`PicusConfigOverlay`].
    pub fn parse_overlay_toml(s: &str) -> Result<PicusConfigOverlay, PicusError> {
        toml::from_str(s)
            .map_err(|e| PicusError::Config(format!("config parse error: {e}")))
    }

    /// Load a config file as an overlay applied onto the compiled
    /// defaults. Convenience for library callers who keep a TOML file.
    pub fn from_file(path: impl AsRef<Path>) -> Result<Self, PicusError> {
        let mut cfg = Self::default();
        let text = read_config_file(path.as_ref())?;
        let overlay = Self::parse_overlay_toml(&text)?;
        cfg.apply_overlay(&overlay)?;
        Ok(cfg)
    }
}

/// Build the effective configuration by layering, in increasing
/// precedence: compiled defaults → config file → CLI overlay. Each
/// layer overrides only the fields it sets; later layers win.
///
/// File selection: the explicit `config_path` (`--config`) if given;
/// otherwise `./picus.toml` in the current directory when it exists;
/// otherwise no file. A missing *explicit* file is an error; a missing
/// auto-discovered `./picus.toml` is silently skipped.
pub fn resolve_config(
    config_path: Option<&Path>,
    cli: &PicusConfigOverlay,
) -> Result<PicusConfig, PicusError> {
    let mut cfg = PicusConfig::default();

    // Layer 1: config file.
    if let Some(path) = resolve_config_path(config_path) {
        let text = read_config_file(&path)?;
        let overlay = PicusConfig::parse_overlay_toml(&text)?;
        cfg.apply_overlay(&overlay)?;
    }

    // Layer 2: CLI flags (highest precedence).
    cfg.apply_overlay(cli)?;

    Ok(cfg)
}

/// Pick the config file to load: explicit `--config` if given, else
/// `./picus.toml` when present, else none.
fn resolve_config_path(explicit: Option<&Path>) -> Option<PathBuf> {
    if let Some(p) = explicit {
        return Some(p.to_path_buf());
    }
    let cwd = PathBuf::from("picus.toml");
    cwd.is_file().then_some(cwd)
}

fn read_config_file(path: &Path) -> Result<String, PicusError> {
    std::fs::read_to_string(path).map_err(|e| {
        PicusError::Config(format!("cannot read config file {}: {e}", path.display()))
    })
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
    config: PicusConfig,
) -> Result<CheckResult, PicusError> {
    // Validate solver/theory combination
    picus_smt::validate_combination(config.analysis.solver, config.analysis.theory)
        .map_err(PicusError::Config)?;

    // Create dump directory if needed
    if let Some(ref dir) = config.analysis.dump_smt {
        let _ = std::fs::create_dir_all(dir);
    }

    // Install the engine config on this thread for the duration of the
    // solve. ConfigGuard restores the prior thread-local on return, so
    // concurrent callers on other threads are unaffected and sequential
    // calls on the same thread can't leak settings into one another.
    let _engine_guard = picus_core::config::ConfigGuard::install(config.engine.clone());

    // Run DPVL on the analysis-layer config.
    let result = picus_analysis::dpvl::run_dpvl(r1cs, &config.analysis)
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
/// `engine.profile_enabled` was set during a previous `check_r1cs` call).
/// `tag` is a free-form label printed alongside the table.
pub fn dump_profile(tag: &str) {
    picus_core::profile::dump_to_stderr(tag);
}

/// Write the accumulated split-GB / DFS counters to stderr (if
/// `engine.gb_stats_enabled` was set during a previous `check_r1cs` call).
pub fn dump_gb_stats() {
    picus_core::profile::dump_split_stats_to_stderr();
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
