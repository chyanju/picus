pub mod aboz;
pub mod basis2;
pub mod bim;
pub mod binary01;
pub mod lemma;
pub mod linear;

pub use binary01::RangeValue;
pub use lemma::{all_descriptors, all_names, LemmaDescriptor, PropagationCtx, PropagationLemma};

use picus_smt::poly_ir::PolyIR;
use std::collections::HashMap;

/// Per-wire connectivity score: the count of distinct constraints whose
/// support touches the wire. Used by the counter-style signal selector
/// to prefer wires that participate in more constraints (and so are
/// more likely to be derivable cheaply).
pub fn wire_connectivity_score(ir: &PolyIR) -> HashMap<usize, usize> {
    use std::collections::HashSet;
    let ring = &ir.ring.ring;
    let n_vars = ring.n_vars();
    let mut counter: HashMap<usize, usize> = HashMap::new();
    for poly in &ir.equalities {
        let mut wires_seen: HashSet<usize> = HashSet::new();
        for (_, m) in ring.terms(poly) {
            for v in 0..n_vars {
                if ring.exponent_at(&m, v) > 0 {
                    let wire = if v < ir.n_wires { v } else { v - ir.n_wires };
                    wires_seen.insert(wire);
                }
            }
        }
        for w in wires_seen {
            *counter.entry(w).or_insert(0) += 1;
        }
    }
    counter
}

