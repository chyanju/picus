//! DPVL algorithm — Decide & Propagate Verification Loop.

use num_bigint::BigUint;
use picus_r1cs::grammar::*;
use picus_r1cs::precondition::Preconditions;
use picus_smt::interpreter::interpret_r1cs;
use picus_smt::optimizer;
use picus_smt::r1cs_parser;
use picus_smt::solver::{self, SolverResult};
use picus_smt::SolverKind;
use std::collections::{HashMap, HashSet};

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

/// Configuration for the DPVL algorithm.
pub struct DpvlConfig {
    pub solver: SolverKind,
    pub selector: SelectorKind,
    pub timeout_ms: u64,
    pub enable_propagation: bool,
    pub enable_solving: bool,
    pub show_smt: bool,
}

/// Internal context holding all DPVL state — eliminates the 12-parameter functions.
struct DpvlContext {
    target_set: HashSet<usize>,
    xlist: Vec<String>,
    alt_xlist: Vec<String>,
    rcdmap: linear::RcdMap,
    /// Optimized constraints (after subp) — used by propagation lemmas.
    p1cnsts: RCmds,
    range_vec: Vec<RangeValue>,
    selector: SelectorState,
    /// Pre-serialized SMT prefix (defs + constraints + alt + preconditions).
    partial_smt: String,
    solver: SolverKind,
    timeout_ms: u64,
    show_smt: bool,
    enable_propagation: bool,
    enable_solving: bool,
}

/// Run the DPVL algorithm on an R1CS file.
pub fn run_dpvl(
    r1cs: &picus_r1cs::grammar::R1csFile,
    config: &DpvlConfig,
    preconditions: Option<&Preconditions>,
) -> DpvlResult {
    let nwires = r1cs.n_wires() as usize;
    let input_set: HashSet<usize> = r1cs.inputs.iter().copied().collect();
    let output_set: HashSet<usize> = r1cs.outputs.iter().copied().collect();

    // Check uniqueness of output signals (weak uniqueness per QED² paper).
    let target_set = output_set;

    // Parse original + alternative constraints
    let parsed = r1cs_parser::parse_r1cs(r1cs, &[], config.solver);
    let xlist = parsed.xlist.clone();

    let alt_xlist: Vec<String> = (0..nwires)
        .map(|i| {
            if input_set.contains(&i) {
                format!("x{}", i)
            } else {
                format!("y{}", i)
            }
        })
        .collect();

    let alt_parsed = r1cs_parser::parse_r1cs(r1cs, &alt_xlist, config.solver);

    // Optimization pipeline: original
    let p0cnsts = optimizer::optimize_p0(&parsed.cnsts, config.solver);
    let expcnsts = r1cs_parser::expand_r1cs(&p0cnsts, config.solver);
    let nrmcnsts = optimizer::normalize(&expcnsts, config.solver);
    let (p1cnsts, p1decls) = optimizer::optimize_p1(&nrmcnsts, &parsed.decls, config.solver, true);

    // For rcdmap
    let sdm_exp = r1cs_parser::expand_r1cs(&parsed.cnsts, config.solver);
    let sdmcnsts = optimizer::normalize(&sdm_exp, config.solver);

    // Alternative pipeline
    let alt_p0 = optimizer::optimize_p0(&alt_parsed.cnsts, config.solver);
    let alt_exp = r1cs_parser::expand_r1cs(&alt_p0, config.solver);
    let alt_nrm = optimizer::normalize(&alt_exp, config.solver);
    let (alt_p1cnsts, alt_p1decls) =
        optimizer::optimize_p1(&alt_nrm, &alt_parsed.decls, config.solver, false);

    // Known/unknown sets
    let mut ks: HashSet<usize> = input_set;
    let mut us: HashSet<usize> = (0..nwires).filter(|i| !ks.contains(i)).collect();

    if let Some(pre) = preconditions {
        for &sig in &pre.unique_set {
            ks.insert(sig);
            us.remove(&sig);
        }
    }

    // Build partial commands and pre-serialize to SMT string
    let mut partial_cmds = Vec::new();
    partial_cmds.extend(p1decls.commands);
    partial_cmds.extend(p1cnsts.commands.iter().cloned());
    partial_cmds.extend(alt_p1decls.commands);
    partial_cmds.extend(alt_p1cnsts.commands);

    // Explicitly assert x0 = 1 for both copies.
    // The simple optimizer replaces Var("x0") with Int(1) everywhere,
    // which turns the original "assert (= 1 x0)" into a tautology.
    // We must re-assert it so the declared x0 variable is constrained.
    partial_cmds.push(RCmd::Assert(RExpr::Eq(
        Box::new(RExpr::Var(xlist[0].clone())),
        Box::new(RExpr::Int(BigUint::from(1u32))),
    )));
    partial_cmds.push(RCmd::Assert(RExpr::Eq(
        Box::new(RExpr::Var(alt_xlist[0].clone())),
        Box::new(RExpr::Int(BigUint::from(1u32))),
    )));

    if let Some(pre) = preconditions {
        for (_tag, cmd) in &pre.commands {
            partial_cmds.push(cmd.clone());
        }
    }

    let partial_rcmds = RCmds::new(partial_cmds);
    let opts_str = interpret_r1cs(&parsed.opts, config.solver);
    let partial_smt = format!("{}{}", opts_str, interpret_r1cs(&partial_rcmds, config.solver));

    // Initialize range vector
    let mut range_vec: Vec<RangeValue> = (0..nwires).map(|_| RangeValue::Bottom).collect();
    range_vec[0] = RangeValue::Values([BigUint::from(1u32)].into_iter().collect());

    let rcdmap = linear::compute_rcdmap(&sdmcnsts);

    let mut ctx = DpvlContext {
        target_set,
        xlist,
        alt_xlist,
        rcdmap,
        p1cnsts,
        range_vec,
        selector: SelectorState::new(config.selector),
        partial_smt,
        solver: config.solver,
        timeout_ms: config.timeout_ms,
        show_smt: config.show_smt,
        enable_propagation: config.enable_propagation,
        enable_solving: config.enable_solving,
    };

    ctx.iterate(&mut ks, &mut us)
}

impl DpvlContext {
    /// Main DPVL iteration loop (non-recursive).
    fn iterate(&mut self, ks: &mut HashSet<usize>, us: &mut HashSet<usize>) -> DpvlResult {
        loop {
            // Propagate
            if self.enable_propagation {
                self.propagate(ks, us);
            }

            // Check if all targets are known
            if self.target_set.iter().all(|t| ks.contains(t)) {
                return DpvlResult::Safe;
            }

            if !self.enable_solving {
                return DpvlResult::Unknown;
            }

            // Select and solve
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
                        break; // Re-propagate
                    }
                    SolveResult::Sat(model) => {
                        self.selector.feedback(sid, SolverFeedback::Sat);
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
                    continue; // Made some progress, try again
                }
                return if self.target_set.iter().all(|t| ks.contains(t)) {
                    DpvlResult::Safe
                } else {
                    DpvlResult::Unknown
                };
            }
            // made_progress = true → loop back to propagate
        }
    }

    fn propagate(&mut self, ks: &mut HashSet<usize>, us: &mut HashSet<usize>) {
        loop {
            let ks_size = ks.len();

            linear::apply_lemma(&self.rcdmap, ks, us);
            binary01::apply_lemma(ks, us, &self.p1cnsts, &mut self.range_vec);
            basis2::apply_lemma(ks, us, &self.p1cnsts, &self.range_vec);
            aboz::apply_lemma(ks, us, &self.p1cnsts, &self.range_vec);
            bim::apply_lemma(ks, us, &self.p1cnsts, &self.range_vec);

            if ks.len() == ks_size {
                break;
            }
            log::debug!("Propagation round: ks={}, us={}", ks.len(), us.len());
        }
    }

    /// Build and dispatch one SMT query for signal `sid`.
    fn solve(&self, ks: &HashSet<usize>, sid: usize) -> SolveResult {
        // Build per-query commands: known equalities + query assertion + solve
        let mut query_cmds = Vec::new();

        for &j in ks {
            if j < self.xlist.len()
                && j < self.alt_xlist.len()
                && self.xlist[j] != self.alt_xlist[j]
            {
                query_cmds.push(RCmd::Assert(RExpr::Eq(
                    Box::new(RExpr::Var(self.xlist[j].clone())),
                    Box::new(RExpr::Var(self.alt_xlist[j].clone())),
                )));
            }
        }

        if sid < self.xlist.len()
            && sid < self.alt_xlist.len()
            && self.xlist[sid] != self.alt_xlist[sid]
        {
            query_cmds.push(RCmd::Assert(RExpr::Neq(
                Box::new(RExpr::Var(self.xlist[sid].clone())),
                Box::new(RExpr::Var(self.alt_xlist[sid].clone())),
            )));
        }

        query_cmds.push(RCmd::Solve);

        let query_smt = interpret_r1cs(&RCmds::new(query_cmds), self.solver);
        let smt_str = format!("{}{}", self.partial_smt, query_smt);

        log::debug!("SMT query length: {} bytes for signal {}", smt_str.len(), sid);

        if self.show_smt {
            log::info!("SMT file: {:?}", picus_smt::solver::last_smt_path());
        }

        match solver::solve(&smt_str, self.solver, self.timeout_ms) {
            Ok(SolverResult::Unsat) => SolveResult::Verified,
            Ok(SolverResult::Sat(model)) => {
                if self.target_set.contains(&sid) {
                    SolveResult::Sat(model)
                } else {
                    SolveResult::Skip
                }
            }
            Ok(SolverResult::Timeout) | Ok(SolverResult::Unknown) | Ok(SolverResult::Error(_)) => {
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
