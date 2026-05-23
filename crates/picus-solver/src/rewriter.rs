//! FF term canonicalization on `LegacyPolyTerm` lists.
//!
//! Equivalent of cvc5's `theory_ff_rewriter` (`theory/ff/theory_ff_rewriter.cpp`)
//! at the granularity picus-solver works with. cvc5 rewrites on its AST
//! (`FINITE_FIELD_ADD`, `FINITE_FIELD_MULT`, `FINITE_FIELD_NEG`, `EQUAL`);
//! picus-solver receives a flat `Vec<LegacyPolyTerm>` per equality, so the
//! corresponding rewrites are:
//!
//! * Sort variables inside each term (analog of cvc5's child-order
//!   canonicalization under associative-commutative kinds).
//! * Sort terms by variable list, merge consecutive like terms summing
//!   coefficients (analog of `postRewriteFfAdd` like-term combining).
//! * Reduce coefficients modulo `prime` (analog of cvc5's constant
//!   folding).
//! * Drop terms whose coefficient is zero modulo `prime` (analog of
//!   cvc5's drop-zero-summand rule).
//! * Drop equalities whose normalized term list is empty (analog of
//!   `postRewriteFfEq` evaluating `0 = 0` to `true`).

use num_bigint::BigUint;
use num_traits::Zero;

use crate::encoder::{LegacyConstraintSystem, ConstraintSystem, PolyTerm, LegacyPolyTerm};

/// Normalize a `LegacyPolyTerm` list in place.
///
/// On return: each term's `vars` is sorted, terms are sorted by `vars`,
/// like terms are merged with coefficients summed mod `prime`, and any
/// term with a zero coefficient is dropped.
pub fn normalize_term_list(terms: &mut Vec<LegacyPolyTerm>, prime: &BigUint) {
    for t in terms.iter_mut() {
        t.vars.sort();
        if !t.coeff.is_zero() && &t.coeff >= prime {
            t.coeff = &t.coeff % prime;
        }
    }
    terms.sort_by(|a, b| a.vars.cmp(&b.vars));
    let mut write = 0usize;
    for read in 0..terms.len() {
        if write > 0 && terms[write - 1].vars == terms[read].vars {
            let sum = (&terms[write - 1].coeff + &terms[read].coeff) % prime;
            terms[write - 1].coeff = sum;
        } else {
            if read != write {
                terms.swap(read, write);
            }
            write += 1;
        }
    }
    terms.truncate(write);
    terms.retain(|t| !t.coeff.is_zero());
}

/// Normalize every equality in a `LegacyConstraintSystem`. Equalities whose
/// term list is empty after normalization (i.e. `0 = 0` after constant
/// folding and like-term cancellation) are dropped.
pub fn rewrite_system(system: &mut LegacyConstraintSystem) {
    let prime = system.prime.clone();
    let mut new_equalities = Vec::with_capacity(system.equalities.len());
    for mut eq in std::mem::take(&mut system.equalities) {
        normalize_term_list(&mut eq, &prime);
        if eq.is_empty() {
            continue;
        }
        new_equalities.push(eq);
    }
    system.equalities = new_equalities;
}

// ─────────────────────────────────────────────────────────────────────
//   Index-keyed counterparts (Phase 7A6)
// ─────────────────────────────────────────────────────────────────────

/// Normalize an `PolyTerm` list in place. Each term's
/// `vars: Vec<(VarIdx, u16)>` is sorted by index and entries with the
/// same index are merged by adding exponents; terms are sorted by
/// their `vars` slice; like terms (same `vars`) merge coefficients
/// modulo `prime`; terms with zero coefficient are dropped.
pub fn normalize_indexed_term_list(terms: &mut Vec<PolyTerm>, prime: &BigUint) {
    for t in terms.iter_mut() {
        // 1. Within-term: sort by var idx and merge same-idx entries
        //    by summing exponents (handles e.g. `x * x` ↔ `[(x, 2)]`
        //    vs accidentally repeated `[(x, 1), (x, 1)]`).
        t.vars.sort_by_key(|&(idx, _)| idx);
        let mut write = 0usize;
        for read in 0..t.vars.len() {
            if write > 0 && t.vars[write - 1].0 == t.vars[read].0 {
                let combined_exp = t.vars[write - 1].1.saturating_add(t.vars[read].1);
                t.vars[write - 1].1 = combined_exp;
            } else {
                if read != write {
                    t.vars.swap(read, write);
                }
                write += 1;
            }
        }
        t.vars.truncate(write);
        // 2. Coefficient reduction mod prime.
        if !t.coeff.is_zero() && &t.coeff >= prime {
            t.coeff = &t.coeff % prime;
        }
    }
    // 3. Sort terms by var list lexicographically.
    terms.sort_by(|a, b| a.vars.cmp(&b.vars));
    // 4. Merge consecutive like terms by summing coefficients mod p.
    let mut write = 0usize;
    for read in 0..terms.len() {
        if write > 0 && terms[write - 1].vars == terms[read].vars {
            let sum = (&terms[write - 1].coeff + &terms[read].coeff) % prime;
            terms[write - 1].coeff = sum;
        } else {
            if read != write {
                terms.swap(read, write);
            }
            write += 1;
        }
    }
    terms.truncate(write);
    // 5. Drop zero-coefficient terms.
    terms.retain(|t| !t.coeff.is_zero());
}

/// Normalize every equality in an [`ConstraintSystem`].
/// Equalities whose term list collapses to empty are dropped.
pub fn rewrite_indexed_system(system: &mut ConstraintSystem) {
    let prime = system.prime.clone();
    let mut new_equalities = Vec::with_capacity(system.equalities.len());
    for mut eq in std::mem::take(&mut system.equalities) {
        normalize_indexed_term_list(&mut eq, &prime);
        if eq.is_empty() {
            continue;
        }
        new_equalities.push(eq);
    }
    system.equalities = new_equalities;
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    fn term(coeff: u64, vars: &[&str]) -> LegacyPolyTerm {
        LegacyPolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn merge_like_terms() {
        let p = BigUint::from(101u32);
        let mut t = vec![term(2, &["x"]), term(3, &["x"])];
        normalize_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(5u32));
        assert_eq!(t[0].vars, vec!["x".to_string()]);
    }

    #[test]
    fn cancel_to_empty() {
        let p = BigUint::from(101u32);
        // x + (p-1)*x = 0 mod p
        let mut t = vec![term(1, &["x"]), term(100, &["x"])];
        normalize_term_list(&mut t, &p);
        assert!(t.is_empty(), "expected empty after cancellation, got {:?}", t);
    }

    #[test]
    fn sort_vars_within_term_then_merge() {
        let p = BigUint::from(101u32);
        let mut t = vec![term(1, &["x", "y"]), term(1, &["y", "x"])];
        normalize_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(2u32));
        assert_eq!(t[0].vars, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn reduce_coeff_mod_prime() {
        let p = BigUint::from(7u32);
        let mut t = vec![term(10, &["x"])];
        normalize_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(3u32));
    }

    #[test]
    fn distinct_monomials_kept() {
        let p = BigUint::from(101u32);
        let mut t = vec![term(1, &["x", "x"]), term(100, &["x"])];
        normalize_term_list(&mut t, &p);
        assert_eq!(t.len(), 2);
        let by_vars: std::collections::HashMap<Vec<String>, BigUint> =
            t.into_iter().map(|t| (t.vars, t.coeff)).collect();
        assert_eq!(by_vars[&vec!["x".to_string()]], BigUint::from(100u32));
        assert_eq!(
            by_vars[&vec!["x".to_string(), "x".to_string()]],
            BigUint::from(1u32)
        );
    }

    #[test]
    fn drop_zero_coeff_terms() {
        let p = BigUint::from(101u32);
        let mut t = vec![term(0, &["x"]), term(1, &["y"]), term(0, &["z"])];
        normalize_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].vars, vec!["y".to_string()]);
    }

    #[test]
    fn rewrite_system_drops_trivial_equalities() {
        let mut sys = LegacyConstraintSystem {
            prime: BigUint::from(101u32),
            equalities: vec![
                vec![term(1, &["x"]), term(100, &["x"])], // x + (p-1)x = 0  ⇒ true
                vec![term(1, &["y"]), term(1, &["z"])],   // y + z = 0       ⇒ kept
            ],
            disequalities: vec![],
            assignments: vec![],
            add_field_polys: false,
            bitsums: vec![],
        };
        rewrite_system(&mut sys);
        assert_eq!(sys.equalities.len(), 1);
        assert_eq!(sys.equalities[0].len(), 2);
    }

    #[test]
    fn empty_input_stays_empty() {
        let p = BigUint::from(101u32);
        let mut t: Vec<LegacyPolyTerm> = Vec::new();
        normalize_term_list(&mut t, &p);
        assert!(t.is_empty());
    }

    // ── Indexed-term normalize parity tests ──────────────────────

    fn idx_term(coeff: u64, vars: &[(u32, u16)]) -> PolyTerm {
        PolyTerm {
            coeff: BigUint::from(coeff),
            vars: vars.to_vec(),
        }
    }

    #[test]
    fn indexed_merge_like_terms() {
        let p = BigUint::from(101u32);
        // 2*x + 3*x → 5*x. Var index 0.
        let mut t = vec![idx_term(2, &[(0, 1)]), idx_term(3, &[(0, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(5u32));
        assert_eq!(t[0].vars, vec![(0, 1)]);
    }

    #[test]
    fn indexed_cancel_to_empty() {
        let p = BigUint::from(101u32);
        // x + (p-1)x = 0 mod p
        let mut t = vec![idx_term(1, &[(0, 1)]), idx_term(100, &[(0, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert!(t.is_empty());
    }

    #[test]
    fn indexed_sort_within_term_then_merge() {
        let p = BigUint::from(101u32);
        // x*y vs y*x — both represented as `(0,1),(1,1)` after
        // intra-term sort; should merge into `2*x*y`.
        let mut t = vec![idx_term(1, &[(1, 1), (0, 1)]), idx_term(1, &[(0, 1), (1, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(2u32));
        assert_eq!(t[0].vars, vec![(0, 1), (1, 1)]);
    }

    #[test]
    fn indexed_intra_term_exponent_merge() {
        let p = BigUint::from(101u32);
        // [(0,1), (0,1)] should collapse to [(0,2)] (x · x = x^2)
        let mut t = vec![idx_term(1, &[(0, 1), (0, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].vars, vec![(0, 2)]);
    }

    #[test]
    fn indexed_reduce_coeff_mod_prime() {
        let p = BigUint::from(7u32);
        let mut t = vec![idx_term(10, &[(0, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].coeff, BigUint::from(3u32));
    }

    #[test]
    fn indexed_distinct_degrees_kept_separate() {
        let p = BigUint::from(101u32);
        // x^2 and (p-1)*x — distinct monomials.
        let mut t = vec![idx_term(1, &[(0, 2)]), idx_term(100, &[(0, 1)])];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 2);
    }

    #[test]
    fn indexed_drop_zero_coeff() {
        let p = BigUint::from(101u32);
        let mut t = vec![
            idx_term(0, &[(0, 1)]),
            idx_term(1, &[(1, 1)]),
            idx_term(0, &[(2, 1)]),
        ];
        normalize_indexed_term_list(&mut t, &p);
        assert_eq!(t.len(), 1);
        assert_eq!(t[0].vars, vec![(1, 1)]);
    }
}
