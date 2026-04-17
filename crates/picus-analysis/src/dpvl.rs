//! DPVL algorithm — Decide & Propagate Verification Loop.
#![allow(clippy::too_many_arguments)]

use num_bigint::BigUint;
use picus_r1cs::grammar::*;
use picus_r1cs::precondition::Preconditions;
use picus_smt::interpreter::interpret_r1cs;
use picus_smt::optimizer;
use picus_smt::r1cs_parser::{self};
use picus_smt::solver::{self, SolverResult};
use picus_smt::SolverKind;
use std::collections::{HashMap, HashSet};

use crate::propagation::binary01::RangeValue;
use crate::propagation::linear;
use crate::propagation::{aboz, basis2, binary01, bim};
use crate::selector::{SelectorKind, SelectorState, SolverFeedback};

/// DPVL analysis result.
#[derive(Debug, Clone)]
pub enum DpvlResult {
    /// All target signals are uniquely determined.
    Safe,
    /// Found a counterexample: some target signal is not unique.
    Unsafe(HashMap<String, BigUint>),
    /// Could not determine (timeout/no progress).
    Unknown,
}

/// Configuration for the DPVL algorithm.
pub struct DpvlConfig {
    pub solver: SolverKind,
    pub selector: SelectorKind,
    pub timeout_ms: u64,
    pub enable_propagation: bool,
    pub enable_solving: bool,
    pub weak: bool,
    pub show_smt: bool,
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

    // Target set: weak = outputs only, strong = all non-input signals
    let target_set: HashSet<usize> = if config.weak {
        output_set.clone()
    } else {
        (0..nwires).filter(|i| !input_set.contains(i)).collect()
    };

    // Parse original constraints
    let parsed = r1cs_parser::parse_r1cs(r1cs, &[], config.solver);
    let xlist = parsed.xlist.clone();

    // Create alternative variable names: y for non-inputs, x for inputs
    let alt_xlist: Vec<String> = (0..nwires)
        .map(|i| {
            if input_set.contains(&i) {
                format!("x{}", i)
            } else {
                format!("y{}", i)
            }
        })
        .collect();

    // Parse alternative constraints
    let alt_parsed = r1cs_parser::parse_r1cs(r1cs, &alt_xlist, config.solver);

    // Optimization pipeline: original
    let p0cnsts = optimizer::optimize_p0(&parsed.cnsts, config.solver);
    let expcnsts = r1cs_parser::expand_r1cs(&p0cnsts, config.solver);
    let nrmcnsts = optimizer::normalize(&expcnsts, config.solver);
    let (p1cnsts, p1decls) = optimizer::optimize_p1(&nrmcnsts, &parsed.decls, config.solver, true);

    // For rcdmap: use normalized expanded original constraints
    let sdm_exp = r1cs_parser::expand_r1cs(&parsed.cnsts, config.solver);
    let sdmcnsts = optimizer::normalize(&sdm_exp, config.solver);

    // Optimization pipeline: alternative
    let alt_p0 = optimizer::optimize_p0(&alt_parsed.cnsts, config.solver);
    let alt_exp = r1cs_parser::expand_r1cs(&alt_p0, config.solver);
    let alt_nrm = optimizer::normalize(&alt_exp, config.solver);
    let (alt_p1cnsts, alt_p1decls) = optimizer::optimize_p1(&alt_nrm, &alt_parsed.decls, config.solver, false);

    // Known/unknown sets
    let mut ks: HashSet<usize> = input_set.clone();
    let mut us: HashSet<usize> = (0..nwires).filter(|i| !ks.contains(i)).collect();

    // Add precondition unique signals
    if let Some(pre) = preconditions {
        for &sig in &pre.unique_set {
            ks.insert(sig);
            us.remove(&sig);
        }
    }

    // Build partial-cmds (constant prefix for all solver calls)
    let mut partial_cmds = Vec::new();
    partial_cmds.extend(p1decls.vs.iter().cloned());
    partial_cmds.extend(p1cnsts.vs.iter().cloned());
    partial_cmds.extend(alt_p1decls.vs.iter().cloned());
    partial_cmds.extend(alt_p1cnsts.vs.iter().cloned());

    // Add precondition commands
    if let Some(pre) = preconditions {
        for (_tag, cmd) in &pre.commands {
            partial_cmds.push(cmd.clone());
        }
    }

    let partial = RCmds::new(partial_cmds);

    // Initialize range vector
    let mut range_vec: Vec<RangeValue> = (0..nwires).map(|_| RangeValue::Bottom).collect();
    range_vec[0] = RangeValue::Values([BigUint::from(1u32)].into_iter().collect());

    // Initialize selector
    let mut selector = SelectorState::new(config.selector);

    // Compute rcdmap
    let rcdmap = linear::compute_rcdmap(&sdmcnsts);

    // Run DPVL iteration
    dpvl_iterate(
        &mut ks,
        &mut us,
        &target_set,
        &parsed.opts,
        &partial,
        &xlist,
        &alt_xlist,
        &rcdmap,
        &p1cnsts,
        &mut range_vec,
        &mut selector,
        config,
    )
}

fn dpvl_iterate(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    target_set: &HashSet<usize>,
    opts: &RCmds,
    partial: &RCmds,
    xlist: &[String],
    alt_xlist: &[String],
    rcdmap: &linear::RcdMap,
    p1cnsts: &RCmds,
    range_vec: &mut Vec<RangeValue>,
    selector: &mut SelectorState,
    config: &DpvlConfig,
) -> DpvlResult {
    // Propagate
    if config.enable_propagation {
        dpvl_propagate(ks, us, rcdmap, p1cnsts, range_vec);
    }

    // Check if all targets are known
    if target_set.iter().all(|t| ks.contains(t)) {
        return DpvlResult::Safe;
    }

    if !config.enable_solving {
        return DpvlResult::Unknown;
    }

    // Select and solve
    let us_before = us.len();
    let mut uspool: HashSet<usize> = us.clone();

    loop {
        if uspool.is_empty() {
            break;
        }

        let sid = match selector.select(&uspool, rcdmap) {
            Some(s) => s,
            None => break,
        };

        uspool.remove(&sid);

        log::debug!("Solving signal {} (target={})", sid, target_set.contains(&sid));
        let result = dpvl_solve(ks, sid, opts, partial, xlist, alt_xlist, target_set, config);
        log::debug!("Signal {} result: {:?}", sid, match &result {
            SolveResult::Verified => "verified".to_string(),
            SolveResult::Sat(_) => "sat".to_string(),
            SolveResult::Skip => "skip".to_string(),
        });

        match result {
            SolveResult::Verified => {
                selector.feedback(sid, SolverFeedback::Verified);
                ks.insert(sid);
                us.remove(&sid);

                // Recurse: re-propagate and continue
                return dpvl_iterate(
                    ks, us, target_set, opts, partial, xlist, alt_xlist, rcdmap, p1cnsts,
                    range_vec, selector, config,
                );
            }
            SolveResult::Sat(model) => {
                selector.feedback(sid, SolverFeedback::Sat);
                if target_set.contains(&sid) {
                    return DpvlResult::Unsafe(model);
                }
                // Non-target SAT: skip
                selector.feedback(sid, SolverFeedback::Skip);
            }
            SolveResult::Skip => {
                selector.feedback(sid, SolverFeedback::Skip);
            }
        }
    }

    // Check if we made progress
    if us.len() < us_before {
        // Made progress via solving, continue
        dpvl_iterate(
            ks, us, target_set, opts, partial, xlist, alt_xlist, rcdmap, p1cnsts, range_vec,
            selector, config,
        )
    } else if target_set.iter().all(|t| ks.contains(t)) {
        DpvlResult::Safe
    } else {
        DpvlResult::Unknown
    }
}

fn dpvl_propagate(
    ks: &mut HashSet<usize>,
    us: &mut HashSet<usize>,
    rcdmap: &linear::RcdMap,
    p1cnsts: &RCmds,
    range_vec: &mut [RangeValue],
) {
    loop {
        let ks_size = ks.len();

        // L0: Linear lemma
        let (new_ks, new_us) = linear::apply_lemma(rcdmap, ks.clone(), us.clone());
        *ks = new_ks;
        *us = new_us;

        // L1: Binary01 lemma
        let (new_ks, new_us) = binary01::apply_lemma(ks.clone(), us.clone(), p1cnsts, range_vec);
        *ks = new_ks;
        *us = new_us;

        // L2: Basis2 lemma
        let (new_ks, new_us) = basis2::apply_lemma(ks.clone(), us.clone(), p1cnsts, range_vec);
        *ks = new_ks;
        *us = new_us;

        // L3: ABOZ lemma
        let (new_ks, new_us) = aboz::apply_lemma(ks.clone(), us.clone(), p1cnsts, range_vec);
        *ks = new_ks;
        *us = new_us;

        // L4: BIM lemma
        let (new_ks, new_us) = bim::apply_lemma(ks.clone(), us.clone(), p1cnsts, range_vec);
        *ks = new_ks;
        *us = new_us;

        // Check for fixed point
        if ks.len() == ks_size {
            break;
        }
    }
}

enum SolveResult {
    Verified,
    Sat(HashMap<String, BigUint>),
    Skip,
}

fn dpvl_solve(
    ks: &HashSet<usize>,
    sid: usize,
    opts: &RCmds,
    partial: &RCmds,
    xlist: &[String],
    alt_xlist: &[String],
    target_set: &HashSet<usize>,
    config: &DpvlConfig,
) -> SolveResult {
    // Build known-equality assertions: assert(x[j] == y[j]) for all j in ks
    let mut final_cmds = Vec::new();
    final_cmds.extend(partial.vs.iter().cloned());

    for &j in ks {
        if j < xlist.len() && j < alt_xlist.len() && xlist[j] != alt_xlist[j] {
            final_cmds.push(RCmd::Assert(RExpr::Eq(
                Box::new(RExpr::Var(xlist[j].clone())),
                Box::new(RExpr::Var(alt_xlist[j].clone())),
            )));
        }
    }

    // Query: assert(x[sid] != y[sid])
    if sid < xlist.len() && sid < alt_xlist.len() && xlist[sid] != alt_xlist[sid] {
        final_cmds.push(RCmd::Assert(RExpr::Neq(
            Box::new(RExpr::Var(xlist[sid].clone())),
            Box::new(RExpr::Var(alt_xlist[sid].clone())),
        )));
    }

    final_cmds.push(RCmd::Solve);

    let final_rcmds = RCmds::new(final_cmds);

    // Generate SMT string
    let opts_str = interpret_r1cs(opts, config.solver);
    let body_str = interpret_r1cs(&final_rcmds, config.solver);
    let smt_str = format!("{}{}", opts_str, body_str);

    log::debug!("SMT query length: {} bytes for signal {}", smt_str.len(), sid);
    log::trace!("SMT query:\n{}", &smt_str[..smt_str.len().min(500)]);

    if config.show_smt {
        log::info!("SMT file: {:?}", picus_smt::solver::last_smt_path());
    }

    // Invoke solver
    match solver::solve(&smt_str, config.solver, config.timeout_ms) {
        Ok(SolverResult::Unsat) => SolveResult::Verified,
        Ok(SolverResult::Sat(model)) => {
            if target_set.contains(&sid) {
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
