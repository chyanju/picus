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
