pub mod aboz;
pub mod basis2;
pub mod bim;
pub mod binary01;
pub mod lemma;
pub mod linear;
pub mod range;

pub use lemma::{all_descriptors, all_names, LemmaDescriptor, PropagationCtx, PropagationLemma};
pub use range::{initial_ranges, RangeValue};

use picus_smt::poly_ir::PolyIR;
use std::collections::HashMap;

/// Per-wire connectivity score: the count of distinct constraints whose
/// support touches the wire. Used by the counter-style signal selector
/// to prefer wires that participate in more constraints (and so are
/// more likely to be derivable cheaply).
///
/// Iterates only over the variables that actually appear in each
/// polynomial (`PolyRingFacade::appearing_indeterminates`) rather
/// than scanning all `2 * n_wires` ring variables per monomial. On a
/// 100k-wire IR with a few terms per constraint this is the
/// difference between O(n^2) and O(constraints * support).
pub fn wire_connectivity_score(ir: &PolyIR) -> HashMap<usize, usize> {
    use std::collections::HashSet;
    let mut counter: HashMap<usize, usize> = HashMap::new();
    for poly in &ir.equalities {
        let mut wires_seen: HashSet<usize> = HashSet::new();
        let vars = ir.ring.ring.appearing_indeterminates(poly);
        for v in vars.iter() {
            wires_seen.insert(ir.var_to_wire(v));
        }
        for w in wires_seen {
            *counter.entry(w).or_insert(0) += 1;
        }
    }
    counter
}

