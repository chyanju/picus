//! L0: Linear lemma — constraint dependency propagation.

use picus_r1cs::grammar::*;
use std::collections::{HashMap, HashSet};

/// Constraint Dependency Map: signal → list of dependency sets.
pub type CdMap = HashMap<usize, Vec<HashSet<usize>>>;

/// Reversed CDMap: dependency set (sorted vec) → set of deducible signals.
pub type RcdMap = HashMap<Vec<usize>, HashSet<usize>>;

/// Build the rcdmap from constraint AST.
#[must_use]
pub fn compute_rcdmap(cnsts: &RCmds) -> RcdMap {
    let cdmap = compute_cdmap(cnsts);
    invert_cdmap(&cdmap)
}

fn compute_cdmap(cnsts: &RCmds) -> CdMap {
    let mut cdmap: CdMap = HashMap::new();

    for cmd in &cnsts.commands {
        if let RCmd::Assert(expr) = cmd {
            let all_vars: HashSet<usize> = expr
                .get_variables(true)
                .into_iter()
                .filter_map(|v| match v {
                    VarRef::Index(i) => Some(i),
                    _ => None,
                })
                .collect();

            let linear_vars: HashSet<usize> = expr
                .get_linear_variables(true)
                .into_iter()
                .filter_map(|v| match v {
                    VarRef::Index(i) => Some(i),
                    _ => None,
                })
                .collect();

            let nonlinear_vars: HashSet<usize> = expr
                .get_nonlinear_variables(true)
                .into_iter()
                .filter_map(|v| match v {
                    VarRef::Index(i) => Some(i),
                    _ => None,
                })
                .collect();

            for &var in &linear_vars {
                if nonlinear_vars.contains(&var) {
                    continue;
                }
                let deps: HashSet<usize> = all_vars.iter().copied().filter(|&v| v != var).collect();
                cdmap.entry(var).or_default().push(deps);
            }
        }
    }

    cdmap
}

fn invert_cdmap(cdmap: &CdMap) -> RcdMap {
    let mut rcdmap: RcdMap = HashMap::new();
    for (&signal, dep_sets) in cdmap {
        for deps in dep_sets {
            let mut key: Vec<usize> = deps.iter().copied().collect();
            key.sort();
            rcdmap.entry(key).or_default().insert(signal);
        }
    }
    rcdmap
}

/// Apply the linear lemma: fixed-point propagation using rcdmap.
/// Mutates `ks` and `us` in place.
pub fn apply_lemma(rcdmap: &RcdMap, ks: &mut HashSet<usize>, us: &mut HashSet<usize>) {
    loop {
        let mut changed = false;
        for (dep_key, deducible) in rcdmap {
            let all_known = dep_key.iter().all(|d| ks.contains(d));
            if all_known {
                for &sig in deducible {
                    if us.remove(&sig) {
                        ks.insert(sig);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}
