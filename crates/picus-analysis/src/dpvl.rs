//! DPVL algorithm — Decide & Propagate Verification Loop.
//!
//! The driver runs in two interlocking layers:
//!
//! 1. **Propagation**: registered [`PropagationLemma`] plugins run to a
//!    fixed point against a single [`PolyIR`], marking wires as known
//!    in [`PropagationCtx`]. Constraints learned by lemmas are folded
//!    into the IR at the end of each outer iteration so the next
//!    iteration sees them.
//! 2. **Solver dispatch**: when propagation no longer makes progress
//!    and target signals remain unverified, the selector picks an
//!    unknown wire and the configured backend tries to prove its
//!    uniqueness (UNSAT ⇒ verified). A SAT result on a target signal
//!    is reported back as a counter-example.
//!
//! Backends consume the same [`PolyIR`] the propagation layer builds;
//! before each solve the driver appends `x_w - y_w = 0` equalities for
//! every newly-proved-unique wire and sets `target_signal` so the
//! backend's closing `(not (= x_target y_target))` matches.

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use picus_r1cs::grammar::*;
use picus_smt::backends::{SolverBackend, SolverResult};
use picus_smt::poly_ir::{r1cs_to_poly_ir, LowerError, PolyIR};
use picus_smt::{SolverKind, Theory};
use picus_core::poly::IrPoly as Poly;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::propagation::range::{initial_ranges, RangeValue};
use crate::propagation::{
    all_descriptors, all_names, wire_connectivity_score, PropagationCtx, PropagationLemma,
};
use crate::selector::{SelectorKind, SelectorState, SolverFeedback};

/// DPVL analysis result.
#[derive(Debug, Clone)]
pub enum DpvlResult {
    Safe,
    Unsafe(HashMap<String, BigUint>),
    Unknown,
}

/// Caller-facing selection of which propagation lemmas to run.
///
/// Names are resolved against the live `inventory` registry; an
/// unknown name in `--lemmas` is an error. Default is "all enabled".
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LemmaSet {
    enabled: HashSet<String>,
}

impl LemmaSet {
    /// Every registered lemma enabled.
    pub fn all() -> Self {
        Self {
            enabled: all_names().iter().map(|s| s.to_string()).collect(),
        }
    }

    /// No lemmas enabled (solver-only mode).
    pub fn none() -> Self {
        Self {
            enabled: HashSet::new(),
        }
    }

    /// Parse a `--lemmas` spec.
    ///
    /// Formats:
    /// - `all` — enable every registered lemma
    /// - `none` — disable every registered lemma
    /// - `all-X,Y` — all except `X` and `Y`
    /// - `none+X,Y` — none except `X` and `Y`
    /// - `X,Y` — explicit list (same as `none+X,Y`)
    pub fn parse(s: &str) -> Result<Self, String> {
        let s = s.trim().to_lowercase();
        let names: Vec<String> = all_names().iter().map(|s| s.to_string()).collect();
        let names_set: HashSet<&str> = names.iter().map(|s| s.as_str()).collect();

        if s == "all" {
            return Ok(Self::all());
        }
        if s == "none" {
            return Ok(Self::none());
        }

        if let Some(rest) = s.strip_prefix("all-") {
            let mut set = Self::all();
            for name in rest.split(',') {
                let name = name.trim();
                Self::check_name(name, &names_set)?;
                set.enabled.remove(name);
            }
            return Ok(set);
        }

        let bare = if let Some(rest) = s.strip_prefix("none+") {
            rest
        } else {
            &s[..]
        };
        let mut set = Self::none();
        for name in bare.split(',') {
            let name = name.trim();
            Self::check_name(name, &names_set)?;
            set.enabled.insert(name.to_string());
        }
        Ok(set)
    }

    fn check_name(name: &str, valid: &HashSet<&str>) -> Result<(), String> {
        if valid.contains(name) {
            Ok(())
        } else {
            let mut sorted: Vec<&str> = valid.iter().copied().collect();
            sorted.sort();
            Err(format!(
                "unknown lemma: '{}'. Valid: {}",
                name,
                sorted.join(", ")
            ))
        }
    }

    /// Whether `name` is enabled in this set.
    pub fn is_enabled(&self, name: &str) -> bool {
        self.enabled.contains(name)
    }

    /// True iff at least one lemma is enabled.
    pub fn any_enabled(&self) -> bool {
        !self.enabled.is_empty()
    }
}

impl std::fmt::Display for LemmaSet {
    /// Canonical `--lemmas` spec: `none` (empty), `all` (every
    /// registered lemma), or the sorted enabled names joined by `,`.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.enabled.is_empty() {
            return write!(f, "none");
        }
        if self.enabled.len() == all_names().len() {
            return write!(f, "all");
        }
        let mut names: Vec<&str> = self.enabled.iter().map(|s| s.as_str()).collect();
        names.sort_unstable();
        write!(f, "{}", names.join(","))
    }
}

/// Configuration for the DPVL algorithm — the analysis-layer half of
/// the resolved Picus configuration (the engine-layer half lives in
/// [`picus_core::config::RuntimeConfig`]).
#[derive(Debug, Clone, PartialEq)]
pub struct DpvlConfig {
    pub solver: SolverKind,
    pub theory: Theory,
    pub selector: SelectorKind,
    pub timeout_ms: u64,
    pub lemmas: LemmaSet,
    pub dump_smt: Option<PathBuf>,
}

impl Default for DpvlConfig {
    fn default() -> Self {
        Self {
            // Native FF solver is the default: it's the only backend
            // compiled in the default (native-only) build, so a bare
            // `picus check` works without extra Cargo features. cvc5 / z3
            // require their opt-in features and an explicit `--solver`.
            solver: SolverKind::Native,
            theory: Theory::Ff,
            selector: SelectorKind::Counter,
            timeout_ms: 5000,
            lemmas: LemmaSet::all(),
            dump_smt: None,
        }
    }
}

impl DpvlConfig {
    /// Merge the `Some` fields of `o` onto `self`; `None` fields are
    /// left untouched. Enum-valued fields arrive as strings (matching
    /// the CLI and TOML surface) and are parsed here, so a bad value
    /// surfaces as a config error rather than a silent default.
    pub fn apply_overlay(&mut self, o: &DpvlOverlay) -> Result<(), String> {
        if let Some(s) = &o.solver {
            self.solver = s.parse()?;
        }
        if let Some(s) = &o.theory {
            self.theory = s.parse()?;
        }
        if let Some(s) = &o.selector {
            self.selector = s.parse()?;
        }
        if let Some(v) = o.timeout_ms {
            self.timeout_ms = v;
        }
        if let Some(s) = &o.lemmas {
            self.lemmas = LemmaSet::parse(s)?;
        }
        if let Some(p) = &o.dump_smt {
            self.dump_smt = Some(p.clone());
        }
        Ok(())
    }
}

/// Partial overlay for [`DpvlConfig`]: every field optional, so a config
/// layer (file, CLI) carries only what it sets. Enum fields are raw
/// strings parsed by [`DpvlConfig::apply_overlay`] via the same
/// `FromStr` / [`LemmaSet::parse`] the CLI uses. Merged via
/// `apply_overlay`; later layers win. TOML keys mirror the field names.
#[derive(Default, Debug, Clone, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct DpvlOverlay {
    pub solver: Option<String>,
    pub theory: Option<String>,
    pub selector: Option<String>,
    pub timeout_ms: Option<u64>,
    pub lemmas: Option<String>,
    pub dump_smt: Option<PathBuf>,
}

/// Failure modes of [`run_dpvl`], surfaced as typed variants so callers
/// can distinguish a malformed input (lowering) from a bad solver/theory
/// configuration (backend) rather than parsing a flattened string.
#[derive(Debug, Error)]
pub enum DpvlError {
    #[error("R1CS lowering failed: {0}")]
    Lower(#[from] LowerError),
    #[error("{0}")]
    Backend(String),
}

/// Run DPVL on a parsed R1CS file.
pub fn run_dpvl(r1cs: &R1csFile, config: &DpvlConfig) -> Result<DpvlResult, DpvlError> {
    let nwires = r1cs.n_wires() as usize;
    let input_set: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let output_set: HashSet<usize> = r1cs.outputs.iter().copied().collect();
    let target_set = output_set;

    let mut ks: HashSet<usize> = input_set.clone();
    let mut us: HashSet<usize> = (0..nwires).filter(|i| !ks.contains(i)).collect();
    let mut ranges: HashMap<usize, RangeValue> = initial_ranges();

    // Lower R1CS → PolyIR once per DPVL run. The target signal stored in
    // the IR is a placeholder; propagation only consumes the constraint
    // set and metadata, not `target_signal`.
    let mut ir = r1cs_to_poly_ir(r1cs, &ks, 0)?;

    // Instantiate enabled lemma plugins.
    let mut lemma_instances: Vec<Box<dyn PropagationLemma>> = all_descriptors()
        .iter()
        .filter(|d| config.lemmas.is_enabled(d.name))
        .map(|d| (d.factory)())
        .collect();

    // Per-wire connectivity score for the counter selector.
    let connectivity = wire_connectivity_score(&ir);

    let backend =
        picus_smt::create_backend(config.solver, config.theory).map_err(DpvlError::Backend)?;
    let mut ctx = DpvlContext {
        target_set,
        selector: SelectorState::new(config.selector, connectivity),
        backend,
        timeout_ms: config.timeout_ms,
        dump_smt: config.dump_smt.clone(),
    };
    Ok(ctx.iterate(&mut ir, &mut lemma_instances, &mut ks, &mut us, &mut ranges))
}

struct DpvlContext {
    target_set: HashSet<usize>,
    selector: SelectorState,
    backend: Option<Box<dyn SolverBackend>>,
    timeout_ms: u64,
    dump_smt: Option<PathBuf>,
}

impl DpvlContext {
    fn iterate(
        &mut self,
        ir: &mut PolyIR,
        lemmas: &mut [Box<dyn PropagationLemma>],
        ks: &mut HashSet<usize>,
        us: &mut HashSet<usize>,
        ranges: &mut HashMap<usize, RangeValue>,
    ) -> DpvlResult {
        loop {
            if !lemmas.is_empty() {
                self.propagate(ir, lemmas, ks, us, ranges);
            }

            // Sync newly-known wires from propagation into the IR so
            // the next backend call sees `x_w - y_w = 0` for them.
            for &w in ks.iter() {
                ir.add_known_wire(w);
            }

            if self.target_set.iter().all(|t| ks.contains(t)) {
                return DpvlResult::Safe;
            }

            if self.backend.is_none() {
                return DpvlResult::Unknown;
            }

            let mut uspool: HashSet<usize> = us.clone();
            let mut made_progress = false;

            loop {
                if uspool.is_empty() {
                    break;
                }
                let sid = match self.selector.select(&uspool) {
                    Some(s) => s,
                    None => break,
                };
                uspool.remove(&sid);

                log::debug!(
                    "Solving signal {} (target={})",
                    sid,
                    self.target_set.contains(&sid)
                );
                let result = self.solve(ir, sid);

                match result {
                    SolveResult::Verified => {
                        self.selector.feedback(sid, SolverFeedback::Verified);
                        ks.insert(sid);
                        us.remove(&sid);
                        ir.add_known_wire(sid);
                        made_progress = true;
                        break;
                    }
                    SolveResult::Sat(model) => {
                        if self.target_set.contains(&sid) {
                            return DpvlResult::Unsafe(model);
                        }
                        self.selector.feedback(sid, SolverFeedback::Skip);
                    }
                    SolveResult::Skip => {
                        self.selector.feedback(sid, SolverFeedback::Skip);
                    }
                }
            }

            if !made_progress {
                // No wire was verified this round (the only `us`-shrinking
                // path, `Verified`, sets `made_progress`), so `us` is
                // unchanged and another iteration cannot help: decide now.
                return if self.target_set.iter().all(|t| ks.contains(t)) {
                    DpvlResult::Safe
                } else {
                    DpvlResult::Unknown
                };
            }
        }
    }

    /// Run every enabled lemma to a fixed point. Each outer iteration
    /// invokes every lemma once with the current IR snapshot; learned
    /// equalities and disjunctions are then folded back into the IR
    /// so the next iteration's lemmas see the new facts.
    ///
    /// The fixed-point detector recognises four kinds of progress:
    ///   * `ks.len()` grew,
    ///   * some lemma's `run` returned `true`,
    ///   * the equality out-buffer received a polynomial,
    ///   * the disjunction out-buffer received a clause.
    /// A lemma whose only output is a tightened range or a new
    /// learned constraint counts as progress and triggers another
    /// iteration. Per-lemma contribution counts are emitted at
    /// `debug!` for ablation work.
    fn propagate(
        &mut self,
        ir: &mut PolyIR,
        lemmas: &mut [Box<dyn PropagationLemma>],
        ks: &mut HashSet<usize>,
        us: &mut HashSet<usize>,
        ranges: &mut HashMap<usize, RangeValue>,
    ) {
        loop {
            let ks_before = ks.len();
            let mut learned_eqs: Vec<Poly> = Vec::new();
            let mut learned_disjs: Vec<Vec<Poly>> = Vec::new();
            let mut any_run_progress = false;
            {
                let mut ctx = PropagationCtx {
                    known: ks,
                    unknown: us,
                    ranges,
                    learned: &mut learned_eqs,
                    learned_disjunctions: &mut learned_disjs,
                };
                for lemma in lemmas.iter_mut() {
                    let ks_pre = ctx.known.len();
                    let ranges_pre = ctx.ranges.len();
                    let eqs_pre = ctx.learned.len();
                    let disjs_pre = ctx.learned_disjunctions.len();
                    let p = lemma.run(ir, &mut ctx);
                    log::debug!(
                        "lemma {} fired={} ks+={} ranges+={} eqs+={} disjs+={}",
                        lemma.name(),
                        p,
                        ctx.known.len() - ks_pre,
                        ctx.ranges.len().saturating_sub(ranges_pre),
                        ctx.learned.len() - eqs_pre,
                        ctx.learned_disjunctions.len() - disjs_pre,
                    );
                    any_run_progress |= p;
                }
            }
            let learned_any = !learned_eqs.is_empty() || !learned_disjs.is_empty();
            ir.equalities.extend(learned_eqs);
            ir.disjunctions.extend(learned_disjs);

            let made_progress = any_run_progress || learned_any || ks.len() != ks_before;
            if !made_progress {
                break;
            }
            log::debug!("propagation round: ks={}, us={}", ks.len(), us.len());
        }
    }

    fn solve(&mut self, ir: &mut PolyIR, sid: usize) -> SolveResult {
        let backend = match self.backend.as_mut() {
            Some(b) => b,
            None => return SolveResult::Skip,
        };
        ir.set_target(sid);

        if let Some(ref dir) = self.dump_smt {
            let smt_str = backend.dump_smt(ir);
            let ts = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis();
            let path = dir.join(format!("picus-{}-sig{}.smt2", ts, sid));
            if let Err(e) = std::fs::write(&path, &smt_str) {
                log::warn!("Failed to dump SMT: {}", e);
            } else {
                log::info!("SMT dumped to {}", path.display());
            }
        }

        // DPVL has no external cancel channel of its own; pass a
        // never-firing token so per-call `timeout_ms` is the only
        // budget. Callers wanting interruptible analysis would plumb
        // their own token through `DpvlConfig`.
        let cancel = picus_core::timeout::CancelToken::none();
        match backend.solve(ir, self.timeout_ms, &cancel) {
            Ok(SolverResult::Unsat) => SolveResult::Verified,
            Ok(SolverResult::Sat(model)) => {
                // A SAT model on a target wire is a genuine two-witness
                // counter-example. The native GB solver re-validates
                // every model via `verify_model` before returning SAT,
                // so it cannot emit a spurious one; cvc5's soundness is
                // cvc5's own responsibility, not something we second-
                // guess here.
                if self.target_set.contains(&sid) {
                    SolveResult::Sat(model)
                } else {
                    SolveResult::Skip
                }
            }
            Ok(SolverResult::Unknown(reason)) => {
                log::debug!("solver returned Unknown for wire {}: {:?}", sid, reason);
                SolveResult::Skip
            }
            Err(e) => {
                log::warn!("Solver error: {}", e);
                SolveResult::Skip
            }
        }
    }
}

enum SolveResult {
    Verified,
    Sat(HashMap<String, BigUint>),
    Skip,
}

#[cfg(test)]
#[path = "dpvl_tests.rs"]
mod tests;
