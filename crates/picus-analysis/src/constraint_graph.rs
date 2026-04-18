//! Constraint graph construction and manipulation.

use picus_r1cs::grammar::*;
use picus_r1cs::sym::SymbolMap;
use petgraph::graph::UnGraph;
use std::collections::{BTreeSet, HashMap, HashSet};

/// Constraint graph: signals as nodes, edges from shared constraints.
pub struct ConstraintGraph {
    /// Undirected graph: node index = signal ID.
    pub graph: UnGraph<usize, ()>,
    /// Edge (pair of signal IDs) → set of constraint indices.
    pub edge_to_constraints: HashMap<BTreeSet<usize>, HashSet<usize>>,
    /// Symbol map from .sym file.
    pub sym: Option<SymbolMap>,
}

impl ConstraintGraph {
    /// Build constraint graph from R1CS AST constraints.
    pub fn build(
        cnsts: &RCmds,
        n_wires: usize,
        sym: Option<SymbolMap>,
        detach_x0: bool,
    ) -> Self {
        let mut graph = UnGraph::<usize, ()>::new_undirected();
        let mut node_indices = Vec::with_capacity(n_wires);

        // Create nodes
        for i in 0..n_wires {
            node_indices.push(graph.add_node(i));
        }

        let mut edge_to_constraints: HashMap<BTreeSet<usize>, HashSet<usize>> = HashMap::new();

        // For each constraint, add edges between all pairs of involved signals
        for (cnst_idx, cmd) in cnsts.commands.iter().enumerate() {
            if let RCmd::Assert(expr) = cmd {
                let vars: HashSet<usize> = expr
                    .get_variables(true)
                    .into_iter()
                    .filter_map(|v| match v {
                        VarRef::Index(i) => Some(i),
                        _ => None,
                    })
                    .collect();

                let var_list: Vec<usize> = vars.into_iter().collect();

                for i in 0..var_list.len() {
                    for j in (i + 1)..var_list.len() {
                        let a = var_list[i];
                        let b = var_list[j];

                        if detach_x0 && (a == 0 || b == 0) {
                            continue;
                        }

                        if a < n_wires && b < n_wires {
                            graph.add_edge(node_indices[a], node_indices[b], ());
                            let edge_key: BTreeSet<usize> = [a, b].into_iter().collect();
                            edge_to_constraints
                                .entry(edge_key)
                                .or_default()
                                .insert(cnst_idx);
                        }
                    }
                }
            }
        }

        Self {
            graph,
            edge_to_constraints,
            sym,
        }
    }

    /// Get constraint indices for signals in a given scope.
    pub fn get_scoped_constraint_ids(&self, scope: &HashSet<String>) -> HashSet<usize> {
        let sym = match &self.sym {
            Some(s) => s,
            None => return HashSet::new(),
        };

        let mut constraint_ids = HashSet::new();
        for (edge_key, cnst_ids) in &self.edge_to_constraints {
            let signals: Vec<&usize> = edge_key.iter().collect();
            let in_scope = signals.iter().all(|&&s| {
                sym.scope_vec
                    .get(&s)
                    .map(|sc| !sc.is_disjoint(scope))
                    .unwrap_or(false)
            });
            if in_scope {
                constraint_ids.extend(cnst_ids);
            }
        }
        constraint_ids
    }

    /// Get signals that connect a scope to outside signals.
    pub fn get_connecting_pairs(&self, scope: &HashSet<String>) -> Vec<(usize, usize)> {
        let sym = match &self.sym {
            Some(s) => s,
            None => return Vec::new(),
        };

        let mut pairs = Vec::new();
        for edge_key in self.edge_to_constraints.keys() {
            let sigs: Vec<usize> = edge_key.iter().copied().collect();
            if sigs.len() != 2 {
                continue;
            }

            let in_scope_0 = sym
                .scope_vec
                .get(&sigs[0])
                .map(|sc| !sc.is_disjoint(scope))
                .unwrap_or(false);
            let in_scope_1 = sym
                .scope_vec
                .get(&sigs[1])
                .map(|sc| !sc.is_disjoint(scope))
                .unwrap_or(false);

            if in_scope_0 && !in_scope_1 {
                pairs.push((sigs[0], sigs[1]));
            } else if !in_scope_0 && in_scope_1 {
                pairs.push((sigs[1], sigs[0]));
            }
        }
        pairs
    }
}
