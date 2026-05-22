//! Linear propagation lemma — derives a wire from a set of "if these
//! are known, this one is forced" implications.
//!
//! For each polynomial constraint `p = 0`, partition the variables that
//! actually appear into linear-only (every term containing them has
//! total degree 1) and nonlinear (appear in at least one term of total
//! degree ≥ 2). A purely-linear variable `v` can be eliminated as soon
//! as every other variable in `p` is known, so we record the implication
//! `deps(p, v) → wire(v)`. The lemma applies the implications to a
//! fixed point each iteration.

use std::collections::{HashMap, HashSet};

use inventory;
use picus_smt::poly_ir::PolyIR;
use picus_solver::poly::Poly;

use super::lemma::{LemmaDescriptor, PropagationCtx, PropagationLemma};

#[derive(Default)]
pub struct LinearLemma {
    /// `wire_index → list-of-dependency-sets`. Built lazily on the
    /// first `run` from the equality constraints and cached for the
    /// lifetime of the lemma instance; the IR doesn't shrink during a
    /// DPVL run, so the implications stay valid.
    cdmap: Option<HashMap<usize, Vec<HashSet<usize>>>>,
}

impl PropagationLemma for LinearLemma {
    fn name(&self) -> &'static str {
        "linear"
    }

    fn run(&mut self, ir: &PolyIR, ctx: &mut PropagationCtx) -> bool {
        if self.cdmap.is_none() {
            self.cdmap = Some(build_cdmap(ir));
        }
        let cdmap = self.cdmap.as_ref().unwrap();

        let mut progress = false;
        loop {
            let mut local_progress = false;
            for (&wire, dep_sets) in cdmap.iter() {
                if ctx.known.contains(&wire) {
                    continue;
                }
                if dep_sets
                    .iter()
                    .any(|deps| deps.iter().all(|d| ctx.known.contains(d)))
                    && ctx.unknown.remove(&wire)
                {
                    ctx.known.insert(wire);
                    local_progress = true;
                    progress = true;
                }
            }
            if !local_progress {
                break;
            }
        }
        progress
    }
}

/// Build the constraint-dependency map. Each polynomial yields zero or
/// more `(wire → deps)` entries: for every wire `w` that occurs only
/// linearly in `p`, `deps = wires(p) \ {w}` is one way to deduce `w`.
fn build_cdmap(ir: &PolyIR) -> HashMap<usize, Vec<HashSet<usize>>> {
    let mut cdmap: HashMap<usize, Vec<HashSet<usize>>> = HashMap::new();
    for poly in &ir.equalities {
        let (linear, nonlinear, all) = classify_poly_vars(ir, poly);
        let linear_only: Vec<usize> = linear.difference(&nonlinear).copied().collect();
        for v in linear_only {
            let wire = var_to_wire(ir, v);
            let deps: HashSet<usize> = all
                .iter()
                .filter(|&&u| u != v)
                .map(|&u| var_to_wire(ir, u))
                .filter(|&w| w != wire)
                .collect();
            cdmap.entry(wire).or_default().push(deps);
        }
    }
    cdmap
}

/// Partition the appearing variables of `poly` into (linear, nonlinear,
/// all). A variable is "linear" if it occurs in some total-degree-1
/// term and "nonlinear" if it occurs in any term of total degree ≥ 2.
/// The two sets can overlap (e.g. `x + x*y`); the caller takes the
/// set difference to find purely-linear variables.
fn classify_poly_vars(
    ir: &PolyIR,
    poly: &Poly,
) -> (HashSet<usize>, HashSet<usize>, HashSet<usize>) {
    let ring = &ir.ring.ring;
    let n_vars = ring.n_vars();
    let mut linear = HashSet::new();
    let mut nonlinear = HashSet::new();
    let mut all = HashSet::new();

    for (_, m) in ring.terms(poly) {
        let mut deg_total = 0usize;
        let mut term_vars: Vec<usize> = Vec::new();
        for v in 0..n_vars {
            let e = ring.exponent_at(&m, v);
            if e > 0 {
                deg_total += e;
                term_vars.push(v);
                all.insert(v);
            }
        }
        match deg_total {
            0 => {}
            1 => {
                if let Some(&v) = term_vars.first() {
                    linear.insert(v);
                }
            }
            _ => {
                for v in term_vars {
                    nonlinear.insert(v);
                }
            }
        }
    }
    (linear, nonlinear, all)
}

/// Map a PolyIR variable index back to its underlying wire index. The
/// ring carries `x_i` at index `i` and `y_i` at index `n_wires + i`;
/// both copies refer to the same wire from a propagation standpoint.
fn var_to_wire(ir: &PolyIR, var: usize) -> usize {
    if var < ir.n_wires {
        var
    } else {
        var - ir.n_wires
    }
}

inventory::submit! {
    LemmaDescriptor {
        name: "linear",
        factory: || Box::new(LinearLemma::default()),
    }
}
