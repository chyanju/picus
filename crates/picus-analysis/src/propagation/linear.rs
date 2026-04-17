//! L0: Linear lemma — constraint dependency propagation.
//!
//! For each constraint, identifies linearly-deducible variables and builds
//! a dependency map. Then iterates to fixed point: if all dependencies of
//! a deducible variable are known, mark it as known.

use picus_r1cs::grammar::*;
use std::collections::{HashMap, HashSet};

/// Constraint Dependency Map: signal → list of dependency sets.
/// To deduce signal `s`, ALL signals in at least one dependency set must be known.
pub type CdMap = HashMap<usize, Vec<HashSet<usize>>>;

/// Reversed CDMap: dependency set → set of deducible signals.
pub type RcdMap = HashMap<Vec<usize>, HashSet<usize>>;

/// Build the rcdmap from constraint AST.
pub fn compute_rcdmap(cnsts: &RCmds) -> RcdMap {
    let cdmap = compute_cdmap(cnsts);
    invert_cdmap(&cdmap)
}

/// Build cdmap from constraint commands.
fn compute_cdmap(cnsts: &RCmds) -> CdMap {
    let mut cdmap: CdMap = HashMap::new();

    for cmd in &cnsts.vs {
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

            // A variable is deducible if it appears linearly but NOT nonlinearly
            for &var in &linear_vars {
                if nonlinear_vars.contains(&var) {
                    continue;
                }
                // Dependencies = all other variables in this constraint
                let deps: HashSet<usize> = all_vars.iter().copied().filter(|&v| v != var).collect();
                cdmap.entry(var).or_default().push(deps);
            }
        }
    }

    cdmap
}

/// Invert cdmap: dependency set → deducible signals.
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
///
/// Returns `(new_known_set, new_unknown_set)`.
pub fn apply_lemma(
    rcdmap: &RcdMap,
    mut ks: HashSet<usize>,
    mut us: HashSet<usize>,
) -> (HashSet<usize>, HashSet<usize>) {
    loop {
        let mut changed = false;

        for (dep_key, deducible) in rcdmap {
            // Check if all dependencies are in known set
            let deps_set: HashSet<usize> = dep_key.iter().copied().collect();
            if deps_set.is_subset(&ks) {
                for &sig in deducible {
                    if us.contains(&sig) {
                        ks.insert(sig);
                        us.remove(&sig);
                        changed = true;
                    }
                }
            }
        }

        if !changed {
            break;
        }
    }

    (ks, us)
}
