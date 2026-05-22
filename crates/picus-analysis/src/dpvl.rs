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
use picus_r1cs::grammar::*;
use picus_smt::backends::{SolverBackend, SolverResult};
use picus_smt::poly_ir::{r1cs_to_poly_ir, PolyIR};
use picus_smt::{SolverKind, Theory};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::propagation::binary01::RangeValue;
use crate::propagation::{
    all_descriptors, all_names, binary01, wire_connectivity_score, PropagationCtx,
    PropagationLemma,
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
#[derive(Debug, Clone)]
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

/// Configuration for the DPVL algorithm.
pub struct DpvlConfig {
    pub solver: SolverKind,
    pub theory: Theory,
    pub selector: SelectorKind,
    pub timeout_ms: u64,
    pub lemmas: LemmaSet,
    pub dump_smt: Option<PathBuf>,
}

/// Run DPVL on a parsed R1CS file.
pub fn run_dpvl(r1cs: &R1csFile, config: &DpvlConfig) -> Result<DpvlResult, String> {
    let nwires = r1cs.n_wires() as usize;
    let input_set: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let output_set: HashSet<usize> = r1cs.outputs.iter().copied().collect();
    let target_set = output_set;

    let mut ks: HashSet<usize> = input_set.clone();
    let mut us: HashSet<usize> = (0..nwires).filter(|i| !ks.contains(i)).collect();
    let mut ranges: HashMap<usize, RangeValue> = binary01::initial_ranges();

    // Lower R1CS → PolyIR once per DPVL run. The target signal stored in
    // the IR is a placeholder; propagation only consumes the constraint
    // set and metadata, not `target_signal`.
    let mut ir = r1cs_to_poly_ir(r1cs, &ks, 0);

    // Instantiate enabled lemma plugins.
    let mut lemma_instances: Vec<Box<dyn PropagationLemma>> = all_descriptors()
        .iter()
        .filter(|d| config.lemmas.is_enabled(d.name))
        .map(|d| (d.factory)())
        .collect();

    // Per-wire connectivity score for the counter selector.
    let connectivity = wire_connectivity_score(&ir);

    let backend = picus_smt::create_backend(config.solver, config.theory)?;
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

            let us_before = us.len();
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
                if us.len() < us_before {
                    continue;
                }
                return if self.target_set.iter().all(|t| ks.contains(t)) {
                    DpvlResult::Safe
                } else {
                    DpvlResult::Unknown
                };
            }
        }
    }

    /// Run every enabled lemma to a fixed point. Each outer iteration
    /// invokes every lemma once with the current IR snapshot; the
    /// learned-constraint buffer is then folded back into the IR so
    /// the next iteration's lemmas see the new facts.
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
            let mut learned = Vec::new();
            {
                let mut ctx = PropagationCtx {
                    known: ks,
                    unknown: us,
                    ranges,
                    learned: &mut learned,
                };
                for lemma in lemmas.iter_mut() {
                    lemma.run(ir, &mut ctx);
                }
            }
            ir.equalities.extend(learned);
            if ks.len() == ks_before {
                break;
            }
            log::debug!("Propagation round: ks={}, us={}", ks.len(), us.len());
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

        match backend.solve(ir, self.timeout_ms) {
            Ok(SolverResult::Unsat) => SolveResult::Verified,
            Ok(SolverResult::Sat(model)) => {
                if self.target_set.contains(&sid) {
                    SolveResult::Sat(model)
                } else {
                    SolveResult::Skip
                }
            }
            Ok(SolverResult::Unknown) => SolveResult::Skip,
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
