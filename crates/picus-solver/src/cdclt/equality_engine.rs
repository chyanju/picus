//! Equality engine for atom-level dedup before the FF theory check.
//!
//! Union-find over atom variables: two distinct atom vars whose underlying
//! polynomial equality canonicalises to the same byte sequence share a
//! union-find representative. Asserting one of them then the other at the
//! same polarity is dropped before reaching the GB; opposite polarity is
//! a theory-level conflict.
//!
//! Scope: polynomial-level atom dedup only. Congruence over FF_ADD /
//! FF_MULT / FF_NEG kinds would require a term DAG and is out of scope.

use std::collections::HashMap;

use crate::cdclt::atoms::AtomKey;
use crate::sat::Var;

/// Outcome of `notify`: a fresh fact, a redundant fact, or a contradiction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotifyOutcome {
    /// First time this representative is asserted at this polarity. The
    /// caller should forward to the underlying theory.
    Fresh,
    /// This rep is already asserted at the same polarity. Drop the fact.
    Redundant,
    /// This rep is asserted at the OPPOSITE polarity. Caller should treat
    /// as a theory-level conflict.
    Contradiction,
}

/// Outcome of [`EqualityEngine::register_atom`]. Distinct from
/// [`NotifyOutcome`]: registration is monotonic so `Fresh`/`Redundant`
/// have no meaning, but a union of two classes whose endpoints carry
/// opposite asserted polarities is a theory conflict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegisterOutcome {
    /// Registration completed without exposing a polarity conflict. The
    /// caller need not forward anything to the underlying theory.
    Ok,
    /// The union performed by registration merged two classes whose
    /// previously-asserted polarities disagree. Caller must treat as a
    /// theory-level conflict (the polarity table is left untouched on
    /// this branch, so a subsequent [`notify`] would still see the
    /// per-endpoint disagreement and re-report it).
    Contradiction,
}

/// Union-find equality engine with same-polynomial atom dedup.
pub struct EqualityEngine {
    /// Union-find parent array. `parent[v.0 as usize] = v` for a root.
    parent: Vec<Var>,
    /// Maps canonical poly bytes → an atom var that owns that canon (the
    /// representative for its equivalence class).
    canonical_to_rep: HashMap<Vec<u8>, Var>,
    /// Current polarity asserted on a representative, if any.
    rep_polarity: HashMap<Var, bool>,
    /// Trail of (rep, prior_polarity_state) for push/pop.
    trail: Vec<(Var, Option<bool>)>,
    /// `levels[k]` snapshots `trail.len()` at SAT push k+1.
    levels: Vec<usize>,
}

impl Default for EqualityEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl EqualityEngine {
    pub fn new() -> Self {
        EqualityEngine {
            parent: Vec::new(),
            canonical_to_rep: HashMap::new(),
            rep_polarity: HashMap::new(),
            trail: Vec::new(),
            levels: Vec::new(),
        }
    }

    /// Ensure the union-find has a slot for `v`. Returns its initial rep
    /// (itself).
    fn ensure_slot(&mut self, v: Var) {
        let idx = v.0 as usize;
        while self.parent.len() <= idx {
            let next = Var(self.parent.len() as u32);
            self.parent.push(next);
        }
    }

    fn find(&mut self, v: Var) -> Var {
        self.ensure_slot(v);
        let mut x = v;
        while self.parent[x.0 as usize] != x {
            let p = self.parent[x.0 as usize];
            let gp = self.parent[p.0 as usize];
            self.parent[x.0 as usize] = gp;
            x = gp;
        }
        x
    }

    /// Canonicalise an atom's poly into a byte vector. Same poly → same
    /// bytes; different poly → different bytes (collision-free).
    fn canonicalise(key: &AtomKey) -> Vec<u8> {
        // Sort terms by (sorted-var-names, coeff bytes). Within each term,
        // sort the variable name list so `x*y` and `y*x` collapse.
        let mut terms: Vec<(Vec<String>, Vec<u8>)> = key
            .terms
            .iter()
            .map(|(c, vars)| {
                let mut vs = vars.clone();
                vs.sort();
                (vs, c.to_bytes_be())
            })
            .collect();
        terms.sort();
        let mut out: Vec<u8> = Vec::new();
        for (vars, coeff) in terms {
            out.extend_from_slice(&(vars.len() as u32).to_le_bytes());
            for v in vars {
                out.extend_from_slice(&(v.len() as u32).to_le_bytes());
                out.extend_from_slice(v.as_bytes());
            }
            out.extend_from_slice(&(coeff.len() as u32).to_le_bytes());
            out.extend_from_slice(&coeff);
            out.push(0xFF); // term separator
        }
        out
    }

    /// Register `(var, atom_key)`. If another registered atom has the
    /// same canonical poly, `var` is unioned into that atom's class.
    /// Returns [`RegisterOutcome::Contradiction`] iff the union merges
    /// two classes whose endpoints carry opposite asserted polarities.
    /// On Contradiction the polarity table is left untouched, so a
    /// subsequent [`notify`] on either endpoint trips the same
    /// disagreement.
    pub fn register_atom(&mut self, var: Var, atom: &AtomKey) -> RegisterOutcome {
        self.ensure_slot(var);
        let canon = Self::canonicalise(atom);
        let existing = match self.canonical_to_rep.get(&canon).copied() {
            Some(e) => e,
            None => {
                self.canonical_to_rep.insert(canon, var);
                return RegisterOutcome::Ok;
            }
        };
        let ra = self.find(var);
        let rb = self.find(existing);
        if ra == rb {
            return RegisterOutcome::Ok;
        }
        let pa = self.rep_polarity.get(&ra).copied();
        let pb = self.rep_polarity.get(&rb).copied();
        if let (Some(a), Some(b)) = (pa, pb) {
            if a != b {
                return RegisterOutcome::Contradiction;
            }
        }
        let (lo, hi) = if ra.0 <= rb.0 { (ra, rb) } else { (rb, ra) };
        self.parent[hi.0 as usize] = lo;
        // Migrate any polarity asserted on the absorbed endpoint into the
        // surviving rep so subsequent notify() calls find it.
        if self.rep_polarity.get(&lo).is_none() {
            if let Some(p) = pa.or(pb) {
                self.rep_polarity.insert(lo, p);
            }
        }
        RegisterOutcome::Ok
    }

    /// Notify the engine of a SAT-asserted fact. Returns whether the
    /// caller should forward the fact, drop it, or treat as conflict.
    pub fn notify(&mut self, atom: Var, polarity: bool) -> NotifyOutcome {
        let rep = self.find(atom);
        let prior = self.rep_polarity.get(&rep).copied();
        match prior {
            Some(p) if p == polarity => NotifyOutcome::Redundant,
            Some(_) => NotifyOutcome::Contradiction,
            None => {
                self.trail.push((rep, None));
                self.rep_polarity.insert(rep, polarity);
                NotifyOutcome::Fresh
            }
        }
    }

    /// Save a checkpoint matching a SAT push.
    pub fn push(&mut self) {
        self.levels.push(self.trail.len());
    }

    /// Roll back to the most recent push. Polarities asserted since are
    /// reverted; union-find structure is not (atom registration is
    /// monotonic across SAT decisions).
    pub fn pop(&mut self) {
        if let Some(height) = self.levels.pop() {
            while self.trail.len() > height {
                if let Some((rep, prior)) = self.trail.pop() {
                    match prior {
                        Some(p) => {
                            self.rep_polarity.insert(rep, p);
                        }
                        None => {
                            self.rep_polarity.remove(&rep);
                        }
                    }
                }
            }
        }
    }

    /// Number of distinct fresh facts that have reached `notify` since
    /// construction (or last reset of polarities). Useful for tests.
    pub fn n_fresh_polarities(&self) -> usize {
        self.rep_polarity.len()
    }
}

#[cfg(test)]
#[path = "equality_engine_tests.rs"]
mod tests;
