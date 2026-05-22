//! DPVL algorithm — Decide & Propagate Verification Loop.

use num_bigint::BigUint;
use picus_r1cs::grammar::*;
use picus_smt::backends::{SolverBackend, SolverResult};
use picus_smt::optimizer;
use picus_smt::query::{self};
use picus_smt::r1cs_parser;
use picus_smt::{SolverKind, Theory};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::propagation::binary01::RangeValue;
use crate::propagation::{aboz, basis2, binary01, bim, linear};
use crate::selector::{SelectorKind, SelectorState, SolverFeedback};

/// DPVL analysis result.
#[derive(Debug, Clone)]
pub enum DpvlResult {
    Safe,
    Unsafe(HashMap<String, BigUint>),
    Unknown,
}

/// Set of enabled propagation lemmas.
#[derive(Debug, Clone)]
pub struct LemmaSet {
    pub linear: bool,
    pub binary01: bool,
    pub basis2: bool,
    pub aboz: bool,
    pub bim: bool,
}

impl LemmaSet {
    /// All lemmas enabled.
    pub fn all() -> Self {
        Self { linear: true, binary01: true, basis2: true, aboz: true, bim: true }
    }

    /// No lemmas enabled (solver-only mode, though this is unusual).
    pub fn none() -> Self {
        Self { linear: false, binary01: false, basis2: false, aboz: false, bim: false }
    }

    /// Parse lemma specification string.
    ///
    /// Formats:
    /// - `all` — enable all lemmas
    /// - `none` — disable all lemmas
    /// - `all-linear,bim` — all except linear and bim
    /// - `none+linear,basis2` — none except linear and basis2
    /// - `linear,binary01,basis2` — explicit list (legacy, same as `none+...`)
    pub fn parse(s: &str) -> Result<Self, String> {
        let s = s.trim().to_lowercase();

        if s == "all" {
            return Ok(Self::all());
        }
        if s == "none" {
            return Ok(Self::none());
        }

        // all-X,Y,Z — start from all, exclude listed
        if let Some(rest) = s.strip_prefix("all-") {
            let mut set = Self::all();
            for name in rest.split(',') {
                Self::set_lemma(&mut set, name.trim(), false)?;
            }
            return Ok(set);
        }

        // none+X,Y,Z — start from none, include listed
        if let Some(rest) = s.strip_prefix("none+") {
            let mut set = Self::none();
            for name in rest.split(',') {
                Self::set_lemma(&mut set, name.trim(), true)?;
            }
            return Ok(set);
        }

        // Bare comma-separated list — same as none+...
        let mut set = Self::none();
        for name in s.split(',') {
            Self::set_lemma(&mut set, name.trim(), true)?;
        }
        Ok(set)
    }

    fn set_lemma(set: &mut Self, name: &str, value: bool) -> Result<(), String> {
        match name {
            "linear" => set.linear = value,
            "binary01" => set.binary01 = value,
            "basis2" => set.basis2 = value,
            "aboz" => set.aboz = value,
            "bim" => set.bim = value,
            other => return Err(format!(
                "unknown lemma: '{}'. Valid: linear, binary01, basis2, aboz, bim.",
                other
            )),
        }
        Ok(())
    }

    /// Check if any lemma is enabled.
    pub fn any_enabled(&self) -> bool {
        self.linear || self.binary01 || self.basis2 || self.aboz || self.bim
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

/// Internal context holding all DPVL state.
struct DpvlContext {
    target_set: HashSet<usize>,
    r1cs: picus_r1cs::grammar::R1csFile,
    rcdmap: linear::RcdMap,
    p1cnsts: RCmds,
    range_vec: Vec<RangeValue>,
    selector: SelectorState,
    backend: Option<Box<dyn SolverBackend>>,
    timeout_ms: u64,
    dump_smt: Option<PathBuf>,
    lemmas: LemmaSet,
}

/// Run the DPVL algorithm on an R1CS file.
pub fn run_dpvl(
    r1cs: &picus_r1cs::grammar::R1csFile,
    config: &DpvlConfig,
) -> Result<DpvlResult, String> {
    let nwires = r1cs.n_wires() as usize;
    let input_set: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let output_set: HashSet<usize> = r1cs.outputs.iter().copied().collect();
    let target_set = output_set;

    // --- Propagation pipeline (uses RCmds AST) ---
    // The propagation lemmas operate on AST patterns (Or, Mul, Add, etc.)
    // produced by the parser/optimizer. This is independent of the actual
    // solver backend — solving uses the IR path (UniquenessQuery), not the
    // AST. AB0 rewriting produces the Or patterns that the binary01 lemma
    // matches.
    let parsed = r1cs_parser::parse_r1cs(r1cs, &[]);

    let p0cnsts = optimizer::optimize_p0(&parsed.cnsts);
    let expcnsts = r1cs_parser::expand_r1cs(&p0cnsts);
    let nrmcnsts = optimizer::normalize(&expcnsts);
    let (p1cnsts, _) = optimizer::optimize_p1(&nrmcnsts, &parsed.decls, true);

    let sdm_exp = r1cs_parser::expand_r1cs(&parsed.cnsts);
    let sdmcnsts = optimizer::normalize(&sdm_exp);

    // Known/unknown sets
    let mut ks: HashSet<usize> = input_set;
    let mut us: HashSet<usize> = (0..nwires).filter(|i| !ks.contains(i)).collect();

    // Initialize range vector
    let mut range_vec: Vec<RangeValue> = (0..nwires).map(|_| RangeValue::Bottom).collect();
    range_vec[0] = RangeValue::Values([BigUint::from(1u32)].into_iter().collect());

    let rcdmap = linear::compute_rcdmap(&sdmcnsts);

    // Create solver backend
    let backend = picus_smt::create_backend(config.solver, config.theory)?;

    let mut ctx = DpvlContext {
        target_set,
        r1cs: r1cs.clone(),
        rcdmap,
        p1cnsts,
        range_vec,
        selector: SelectorState::new(config.selector),
        backend,
        timeout_ms: config.timeout_ms,
        dump_smt: config.dump_smt.clone(),
        lemmas: config.lemmas.clone(),
    };

    Ok(ctx.iterate(&mut ks, &mut us))
}

impl DpvlContext {
    fn iterate(&mut self, ks: &mut HashSet<usize>, us: &mut HashSet<usize>) -> DpvlResult {
        loop {
            if self.lemmas.any_enabled() {
                self.propagate(ks, us);
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

                let sid = match self.selector.select(&uspool, &self.rcdmap) {
                    Some(s) => s,
                    None => break,
                };
                uspool.remove(&sid);

                log::debug!("Solving signal {} (target={})", sid, self.target_set.contains(&sid));
                let result = self.solve(ks, sid);

                match result {
                    SolveResult::Verified => {
                        self.selector.feedback(sid, SolverFeedback::Verified);
                        ks.insert(sid);
                        us.remove(&sid);
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

    fn propagate(&mut self, ks: &mut HashSet<usize>, us: &mut HashSet<usize>) {
        loop {
            let ks_size = ks.len();

            if self.lemmas.linear {
                linear::apply_lemma(&self.rcdmap, ks, us);
            }
            if self.lemmas.binary01 {
                binary01::apply_lemma(ks, us, &self.p1cnsts, &mut self.range_vec);
            }
            if self.lemmas.basis2 {
                basis2::apply_lemma(ks, us, &self.p1cnsts, &self.range_vec);
            }
            if self.lemmas.aboz {
                aboz::apply_lemma(ks, us, &self.p1cnsts);
            }
            if self.lemmas.bim {
                bim::apply_lemma(ks, us, &self.p1cnsts);
            }

            if ks.len() == ks_size {
                break;
            }
            log::debug!("Propagation round: ks={}, us={}", ks.len(), us.len());
        }
    }

    fn solve(&mut self, ks: &HashSet<usize>, sid: usize) -> SolveResult {
        let backend = match self.backend.as_mut() {
            Some(b) => b,
            None => return SolveResult::Skip,
        };

        let query_ir = query::build_query(&self.r1cs, ks, sid);

        // Optionally dump SMT
        if let Some(ref dir) = self.dump_smt {
            let smt_str = backend.dump_smt(&query_ir);
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

        match backend.solve(&query_ir, self.timeout_ms) {
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
