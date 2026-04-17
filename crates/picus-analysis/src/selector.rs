//! Signal selection strategies for the DPVL loop.

use std::collections::{HashMap, HashSet};

use super::propagation::linear::RcdMap;

/// Selector strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectorKind {
    First,
    Counter,
}

impl std::str::FromStr for SelectorKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "first" => Ok(SelectorKind::First),
            "counter" => Ok(SelectorKind::Counter),
            _ => Err(format!("unknown selector: {}", s)),
        }
    }
}

/// Selector state for the counter strategy.
pub struct SelectorState {
    pub kind: SelectorKind,
    pub weights: HashMap<usize, i64>,
    pub rcdkey_counter: Option<HashMap<usize, usize>>,
}

impl SelectorState {
    pub fn new(kind: SelectorKind) -> Self {
        Self {
            kind,
            weights: HashMap::new(),
            rcdkey_counter: None,
        }
    }

    /// Select the next signal to check from the unknown pool.
    pub fn select(&mut self, uspool: &HashSet<usize>, rcdmap: &RcdMap) -> Option<usize> {
        match self.kind {
            SelectorKind::First => uspool.iter().copied().next(),
            SelectorKind::Counter => self.select_counter(uspool, rcdmap),
        }
    }

    /// Provide feedback after a solver call.
    pub fn feedback(&mut self, signal: usize, result: SolverFeedback) {
        if self.kind == SelectorKind::Counter
            && let SolverFeedback::Skip = result {
                *self.weights.entry(signal).or_insert(0) -= 1;
            }
    }

    fn select_counter(&mut self, uspool: &HashSet<usize>, rcdmap: &RcdMap) -> Option<usize> {
        // Lazily build the rcdkey counter
        if self.rcdkey_counter.is_none() {
            let mut counter: HashMap<usize, usize> = HashMap::new();
            for key in rcdmap.keys() {
                for &sig in key {
                    *counter.entry(sig).or_insert(0) += 1;
                }
            }
            self.rcdkey_counter = Some(counter);
        }

        let counter = self.rcdkey_counter.as_ref().unwrap();

        // Select signal with highest score = counter + weight
        uspool
            .iter()
            .copied()
            .max_by_key(|&sig| {
                let c = counter.get(&sig).copied().unwrap_or(0) as i64;
                let w = self.weights.get(&sig).copied().unwrap_or(0);
                c + w
            })
    }
}

/// Feedback from a solver call.
pub enum SolverFeedback {
    Verified,
    Sat,
    Skip,
}
