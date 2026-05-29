//! Signal selection strategies for the DPVL outer loop.

use std::collections::{HashMap, HashSet};

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

/// Per-DPVL-run selector state.
pub struct SelectorState {
    pub kind: SelectorKind,
    /// Negative weights for signals we've skipped this run; used to
    /// deprioritise them on the next pick.
    pub weights: HashMap<usize, i64>,
    /// Constraint-connectivity counter for each wire. Higher count ⇒
    /// the wire participates in more constraints and is likelier to
    /// have a fast deduction path. Built once by the DPVL driver from
    /// the PolyIR and passed to [`SelectorState::select`].
    pub connectivity: HashMap<usize, usize>,
}

impl SelectorState {
    pub fn new(kind: SelectorKind, connectivity: HashMap<usize, usize>) -> Self {
        Self {
            kind,
            weights: HashMap::new(),
            connectivity,
        }
    }

    /// Pick the next signal from the unknown pool to send to the
    /// solver. Returns `None` when the pool is empty.
    pub fn select(&mut self, uspool: &HashSet<usize>) -> Option<usize> {
        match self.kind {
            // Smallest index, not `iter().next()`: HashSet iteration order
            // is nondeterministic across runs/builds, which would make the
            // `first` selector irreproducible.
            SelectorKind::First => uspool.iter().copied().min(),
            SelectorKind::Counter => self.select_counter(uspool),
        }
    }

    /// Record the outcome of a solver call on `signal`.
    pub fn feedback(&mut self, signal: usize, result: SolverFeedback) {
        if self.kind == SelectorKind::Counter
            && let SolverFeedback::Skip = result
        {
            *self.weights.entry(signal).or_insert(0) -= 1;
        }
    }

    fn select_counter(&mut self, uspool: &HashSet<usize>) -> Option<usize> {
        // Highest (connectivity + weight) wins; ties broken by smallest
        // wire index. Folding the index into the key makes every key
        // unique, so the pick is deterministic regardless of the
        // (nondeterministic) HashSet iteration order — matching the
        // reproducibility the `First` selector gets from `.min()`.
        uspool.iter().copied().max_by_key(|&sig| {
            let c = self.connectivity.get(&sig).copied().unwrap_or(0) as i64;
            let w = self.weights.get(&sig).copied().unwrap_or(0);
            (c + w, std::cmp::Reverse(sig))
        })
    }
}

/// Feedback from a solver call.
pub enum SolverFeedback {
    /// Signal was verified as unique (UNSAT).
    Verified,
    /// Signal was skipped (SAT for non-target, timeout, or error).
    Skip,
}

#[cfg(test)]
#[path = "selector_tests.rs"]
mod tests;
