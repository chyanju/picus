//! Native (in-tree GB engine) lowering for [`PolyIR`].
//!
//! These `impl PolyIR` methods produce picus-solver engine types
//! (`ConstraintSystem`, `BooleanQuery`, `EncodedSystem`) plus the linear
//! pre-elimination, so they live with the native backend rather than on
//! the solver-agnostic [`PolyIR`] itself — which then depends only on
//! picus-core. The cvc5 / z3 backends emit SMT-LIB directly from the
//! neutral `PolyIR` surface and do not use these.

use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::Zero;

use picus_core::poly::IrPoly as Poly;
use picus_core::timeout::CancelToken;
use picus_solver::boolean::{BooleanQuery, Formula, Literal};
use picus_solver::frontend::encoder::{
    encode, ConstraintSystem, ConstraintSystemBuilder, EncodedSystem, PolyTerm,
};

use crate::poly_ir::PolyIR;

impl PolyIR {
    /// Linear (Gaussian) pre-elimination — the in-tree analogue of cvc5's
    /// `theory/ff/gauss.cpp`. Computes a Gröbner basis of the linear
    /// equality subsystem (for a linear ideal this is Gaussian
    /// elimination) and reduces every nonlinear equality modulo it,
    /// substituting out the pivot variables. Applied once per top-level
    /// solve so both the conjunctive and CDCL(T) per-check paths consume
    /// the reduced generators (split-GB's `admit` predicate otherwise
    /// strands multi-term linear relations in basis 0).
    ///
    /// Returns `Some(reduced_ir)` when elimination changed the equality
    /// set, else `None` (the caller keeps `self`). Variety-preserving, so
    /// disjunctions / disequalities / metadata carry over unchanged and a
    /// SAT model still verifies against the original system. A linear
    /// subsystem that is itself unsatisfiable collapses the equalities to
    /// a single `1 = 0`, which the solver rejects immediately.
    pub fn pre_eliminate_linear(&self, cancel: &CancelToken) -> Option<PolyIR> {
        let elim =
            picus_solver::gb::linsolve::eliminate_linear(&self.ring, &self.equalities, cancel)
                .ok()?;
        if !elim.applied {
            return None;
        }
        let equalities = if elim.unsat {
            vec![self.ring.one()]
        } else {
            elim.reduced
        };
        Some(PolyIR {
            ring: Arc::clone(&self.ring),
            n_wires: self.n_wires,
            input_indices: self.input_indices.clone(),
            equalities,
            disjunctions: self.disjunctions.clone(),
            known_signals: self.known_signals.clone(),
            target_signal: self.target_signal,
            disequalities: self.disequalities.clone(),
            assignments: self.assignments.clone(),
            bitsums: self.bitsums.clone(),
            add_field_polys: self.add_field_polys,
        })
    }

    /// Lower this `PolyIR` to a [`ConstraintSystem`] via the
    /// `ConstraintSystemBuilder`. Variable names are interned in
    /// `ring.var_names()` order so builder indices match ring
    /// indices; each `Poly` in `self.equalities` yields a
    /// `Vec<PolyTerm>` via [`Self::poly_terms_vec`];
    /// `disequalities`, `assignments`, `bitsums`, and
    /// `add_field_polys` propagate as-is.
    pub fn to_constraint_system(&self) -> ConstraintSystem {
        let prime = self.ring.field().prime().clone();
        let mut builder = ConstraintSystemBuilder::new(prime);
        for name in self.ring.var_names() {
            builder.var(name);
        }
        for poly in &self.equalities {
            let terms = self.poly_terms_vec(poly);
            if !terms.is_empty() {
                builder.add_equality(terms);
            }
        }
        for &(a, b) in &self.disequalities {
            builder.add_disequality(a as u32, b as u32);
        }
        for (v, val) in &self.assignments {
            builder.add_assignment(*v as u32, val.clone());
        }
        for chain in &self.bitsums {
            let bits: Vec<u32> = chain.iter().map(|&v| v as u32).collect();
            builder.add_bitsum(bits);
        }
        builder.set_add_field_polys(self.add_field_polys);
        builder.build()
    }

    /// `poly_terms_idx` collected into the `Vec<PolyTerm>` form that
    /// `Literal` / `add_equality` consume (zero-coeff terms dropped).
    fn poly_terms_vec(&self, poly: &Poly) -> Vec<PolyTerm> {
        self.poly_terms_idx(poly)
            .filter(|(coeff, _)| !coeff.is_zero())
            .map(|(coeff, vars)| PolyTerm {
                coeff,
                vars: vars.into_iter().map(|(v, e)| (v as u32, e)).collect(),
            })
            .collect()
    }

    /// Lower this `PolyIR` to a CDCL(T) [`BooleanQuery`] for the native
    /// solver's disjunction-aware path. The conjunctive constraints
    /// (`equalities`, `assignments`, the target `disequalities`) become
    /// a top-level `And` of `Eq`/`Neq` literals; each clause in
    /// `disjunctions` becomes an `Or` of `Eq` literals. Bitsum chains
    /// are intentionally not materialised here — the CDCL(T) theory
    /// check re-runs `encode` (hence `auto_extract_bitsums`) on each
    /// branch's conjunctive system, so they are recovered there.
    pub fn to_boolean_query(&self) -> BooleanQuery {
        let prime = self.ring.field().prime().clone();
        let mut builder = ConstraintSystemBuilder::new(prime);
        for name in self.ring.var_names() {
            builder.var(name);
        }

        let mut conj: Vec<Formula> = Vec::new();
        for poly in &self.equalities {
            let terms = self.poly_terms_vec(poly);
            if !terms.is_empty() {
                conj.push(Formula::Lit(Literal::Eq(terms, Vec::new())));
            }
        }
        for (v, val) in &self.assignments {
            conj.push(Formula::Lit(Literal::Eq(
                vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(*v as u32, 1)],
                }],
                vec![PolyTerm {
                    coeff: val.clone(),
                    vars: Vec::new(),
                }],
            )));
        }
        for &(a, b) in &self.disequalities {
            conj.push(Formula::Lit(Literal::Neq(
                vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(a as u32, 1)],
                }],
                vec![PolyTerm {
                    coeff: BigUint::from(1u32),
                    vars: vec![(b as u32, 1)],
                }],
            )));
        }
        for clause in &self.disjunctions {
            let lits: Vec<Formula> = clause
                .iter()
                .map(|poly| Formula::Lit(Literal::Eq(self.poly_terms_vec(poly), Vec::new())))
                .collect();
            conj.push(Formula::Or(lits));
        }

        let formula = if conj.is_empty() {
            Formula::True
        } else {
            Formula::And(conj)
        };
        BooleanQuery::from_builder_and_formula(builder, formula)
    }

    /// Encode this `PolyIR` into an [`EncodedSystem`] ready for the
    /// GB engine. Internally builds a `ConstraintSystem` via
    /// [`Self::to_constraint_system`] and routes through
    /// [`picus_solver::frontend::encoder::encode`] (which runs
    /// `rewriter::rewrite_system` and `auto_extract_bitsums`).
    pub fn encode(&self) -> Result<EncodedSystem, String> {
        encode(&self.to_constraint_system())
    }
}
