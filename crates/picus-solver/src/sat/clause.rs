//! Clause storage and references.

use super::lit::Lit;

/// Reference to a clause in a `ClauseArena`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A clause is a disjunction of literals. The first two positions are
/// the watched literals (maintained by the solver); the remaining
/// positions are stored in arbitrary order.
#[derive(Clone, Debug)]
pub struct Clause {
    pub lits: Vec<Lit>,
    /// `true` for learnt clauses (created by conflict analysis);
    /// `false` for input clauses.
    pub learnt: bool,
}

impl Clause {
    pub fn new(lits: Vec<Lit>, learnt: bool) -> Self {
        Clause { lits, learnt }
    }

    pub fn len(&self) -> usize {
        self.lits.len()
    }

    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
}

/// Arena that owns every clause kept by the solver.
#[derive(Default)]
pub struct ClauseArena {
    clauses: Vec<Clause>,
}

impl ClauseArena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, clause: Clause) -> ClauseRef {
        let idx = self.clauses.len();
        self.clauses.push(clause);
        ClauseRef(idx as u32)
    }

    pub fn get(&self, cref: ClauseRef) -> &Clause {
        &self.clauses[cref.index()]
    }

    pub fn get_mut(&mut self, cref: ClauseRef) -> &mut Clause {
        &mut self.clauses[cref.index()]
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (ClauseRef, &Clause)> {
        self.clauses
            .iter()
            .enumerate()
            .map(|(i, c)| (ClauseRef(i as u32), c))
    }
}

#[cfg(test)]
mod tests {
    use super::super::lit::Var;
    use super::*;

    #[test]
    fn arena_add_and_get() {
        let mut a = ClauseArena::new();
        let c1 = a.add(Clause::new(vec![Lit::pos(Var(0)), Lit::neg(Var(1))], false));
        let c2 = a.add(Clause::new(vec![Lit::pos(Var(2))], true));
        assert_eq!(a.len(), 2);
        assert_eq!(a.get(c1).lits.len(), 2);
        assert_eq!(a.get(c2).lits.len(), 1);
        assert!(!a.get(c1).learnt);
        assert!(a.get(c2).learnt);
    }

    #[test]
    fn clause_refs_distinct() {
        let mut a = ClauseArena::new();
        let c1 = a.add(Clause::new(vec![Lit::pos(Var(0))], false));
        let c2 = a.add(Clause::new(vec![Lit::pos(Var(0))], false));
        assert_ne!(c1, c2);
    }
}
