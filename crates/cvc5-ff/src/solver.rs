use cvc5_ff_sys::*;
use std::ffi::CString;
use std::fmt;
use std::marker::PhantomData;

use crate::{
    DatatypeConstructorDecl, Grammar, Proof, Result, Sort, Statistics, SynthResult, Term,
    TermManager,
};

const ERROR_NOT_UTF8: &str = "Not UTF-8";

#[derive(Clone)]
pub enum OptionInfoKind<'a> {
    Void,
    Bool {
        default: bool,
        current: bool,
    },
    String {
        default: &'a str,
        current: &'a str,
    },
    Int64 {
        default: i64,
        current: i64,
        min: Option<i64>,
        max: Option<i64>,
    },
    UInt64 {
        default: u64,
        current: u64,
        min: Option<u64>,
        max: Option<u64>,
    },
    Double {
        default: f64,
        current: f64,
        min: Option<f64>,
        max: Option<f64>,
    },
    Mode {
        default: &'a str,
        current: &'a str,
        modes: Vec<&'a str>,
    },
}

#[derive(Copy, Clone)]
pub struct OptionInfo<'a> {
    inner: cvc5_ff_sys::OptionInfo,
    _phantom: PhantomData<&'a ()>,
}

impl OptionInfo<'_> {
    pub fn kind(&self) -> OptionInfoKind<'_> {
        use cvc5_ff_sys::OptionInfoKind as K;
        match self.inner.kind {
            K::Void => OptionInfoKind::Void,
            K::Bool => OptionInfoKind::Bool {
                default: self.inner.info_bool.dflt,
                current: self.inner.info_bool.cur,
            },
            K::Str => OptionInfoKind::String {
                default: unsafe { std::ffi::CStr::from_ptr(self.inner.info_str.dflt).to_str() }
                    .expect(ERROR_NOT_UTF8),
                current: unsafe { std::ffi::CStr::from_ptr(self.inner.info_str.cur).to_str() }
                    .expect(ERROR_NOT_UTF8),
            },
            K::Int64 => OptionInfoKind::Int64 {
                default: self.inner.info_int.dflt,
                current: self.inner.info_int.cur,
                min: if self.inner.info_int.has_min {
                    Some(self.inner.info_int.min)
                } else {
                    None
                },
                max: if self.inner.info_int.has_max {
                    Some(self.inner.info_int.max)
                } else {
                    None
                },
            },
            K::Uint64 => OptionInfoKind::UInt64 {
                default: self.inner.info_uint.dflt,
                current: self.inner.info_uint.cur,
                min: if self.inner.info_uint.has_min {
                    Some(self.inner.info_uint.min)
                } else {
                    None
                },
                max: if self.inner.info_uint.has_max {
                    Some(self.inner.info_uint.max)
                } else {
                    None
                },
            },
            K::Double => OptionInfoKind::Double {
                default: self.inner.info_double.dflt,
                current: self.inner.info_double.cur,
                min: if self.inner.info_double.has_min {
                    Some(self.inner.info_double.min)
                } else {
                    None
                },
                max: if self.inner.info_double.has_max {
                    Some(self.inner.info_double.max)
                } else {
                    None
                },
            },
            K::Modes => OptionInfoKind::Mode {
                default: unsafe { std::ffi::CStr::from_ptr(self.inner.info_mode.dflt).to_str() }
                    .expect(ERROR_NOT_UTF8),
                current: unsafe { std::ffi::CStr::from_ptr(self.inner.info_mode.cur).to_str() }
                    .expect(ERROR_NOT_UTF8),
                modes: (0..self.inner.info_mode.num_modes)
                    .map(|i| {
                        let p = unsafe { *self.inner.info_mode.modes.add(i) };
                        unsafe { std::ffi::CStr::from_ptr(p).to_str() }.expect(ERROR_NOT_UTF8)
                    })
                    .collect(),
            },
        }
    }
    pub fn category(&self) -> OptionCategory {
        self.inner.category
    }
    pub fn name(&self) -> impl AsRef<str> {
        unsafe { std::ffi::CStr::from_ptr(self.inner.name).to_string_lossy() }
    }
    pub fn is_set_by_user(&self) -> bool {
        self.inner.is_set_by_user
    }
    pub fn aliases(&self) -> Vec<impl AsRef<str>> {
        (0..self.inner.num_aliases)
            .map(|i| {
                let p = unsafe { *self.inner.aliases.add(i) };
                unsafe { std::ffi::CStr::from_ptr(p).to_string_lossy() }
            })
            .collect()
    }
    pub fn no_supports(&self) -> Vec<impl AsRef<str>> {
        (0..self.inner.num_no_supports)
            .map(|i| {
                let p = unsafe { *self.inner.no_supports.add(i) };
                unsafe { std::ffi::CStr::from_ptr(p).to_string_lossy() }
            })
            .collect()
    }
}

impl fmt::Display for OptionInfo<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe {
            std::ffi::CStr::from_ptr(option_info_to_string(&self.inner)).to_string_lossy()
        };
        write!(f, "{}", s)
    }
}

/// A cvc5 solver instance.
///
/// The lifetime `'tm` ties this solver to the [`TermManager`] that created it,
/// ensuring the term manager outlives the solver and all objects it produces.
pub struct Solver<'tm> {
    pub(crate) inner: *mut cvc5_ff_sys::Solver,
    pub(crate) tm: TermManager,
    _phantom: PhantomData<&'tm ()>,
}

impl<'tm> Solver<'tm> {
    /// Create a new solver instance from the given term manager.
    pub fn new(tm: &'tm TermManager) -> Self {
        let tm_clone = tm.clone();
        Self {
            inner: unsafe { new(tm_clone.ptr()) },
            tm: tm_clone,
            _phantom: PhantomData,
        }
    }

    /// Return the underlying term manager
    pub fn term_manager(&self) -> TermManager {
        self.tm.clone()
    }

    // ── Configuration ──────────────────────────────────────────────

    /// Set the logic for this solver (e.g. , ).
    pub fn set_logic(&mut self, logic: &str) {
        let c = CString::new(logic).unwrap();
        unsafe { set_logic(self.inner, c.as_ptr()) }
    }

    /// Return `true` if the logic has been set.
    pub fn is_logic_set(&self) -> bool {
        unsafe { is_logic_set(self.inner) }
    }

    /// Get the currently set logic as a string.
    pub fn get_logic(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(get_logic(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Set a solver option (e.g. `"produce-models"`, `"true"`).
    pub fn set_option(&mut self, option: &str, value: &str) {
        let o = CString::new(option).unwrap();
        let v = CString::new(value).unwrap();
        unsafe { set_option(self.inner, o.as_ptr(), v.as_ptr()) }
    }

    /// Get the current value of a solver option.
    pub fn get_option(&self, option: &str) -> String {
        let o = CString::new(option).unwrap();
        unsafe {
            std::ffi::CStr::from_ptr(get_option(self.inner, o.as_ptr()))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Get the list of all option names.
    pub fn get_option_names(&self) -> Vec<String> {
        let mut size = 0usize;
        let ptr = unsafe { get_option_names(self.inner, &mut size) };
        (0..size)
            .map(|i| unsafe {
                std::ffi::CStr::from_ptr(*ptr.add(i))
                    .to_string_lossy()
                    .into_owned()
            })
            .collect()
    }

    /// Set solver information (SMT-LIB `set-info`).
    pub fn set_info(&mut self, keyword: &str, value: &str) {
        let k = CString::new(keyword).unwrap();
        let v = CString::new(value).unwrap();
        unsafe { set_info(self.inner, k.as_ptr(), v.as_ptr()) }
    }

    /// Get solver information (SMT-LIB `get-info`).
    pub fn get_info(&self, flag: &str) -> String {
        let f = CString::new(flag).unwrap();
        unsafe {
            std::ffi::CStr::from_ptr(get_info(self.inner, f.as_ptr()))
                .to_string_lossy()
                .into_owned()
        }
    }

    // ── Assertions & checking ──────────────────────────────────────

    /// Assert a formula to the solver.
    pub fn assert_formula(&mut self, term: Term) {
        unsafe { assert_formula(self.inner, term.inner) }
    }

    /// Check satisfiability of the current assertions.
    pub fn check_sat(&mut self) -> Result<'tm> {
        Result::from_raw(unsafe { check_sat(self.inner) })
    }

    /// Check satisfiability under the given assumptions.
    pub fn check_sat_assuming(&mut self, assumptions: &[Term]) -> Result<'tm> {
        let raw: Vec<cvc5_ff_sys::Term> = assumptions.iter().map(|t| t.inner).collect();
        Result::from_raw(unsafe { check_sat_assuming(self.inner, raw.len(), raw.as_ptr()) })
    }

    /// Get the list of asserted formulas.
    pub fn get_assertions(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_assertions(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    // ── Simplification ─────────────────────────────────────────────

    /// Simplify a term. If `apply_subs` is true, apply learned substitutions.
    pub fn simplify(&self, term: Term, apply_subs: bool) -> Term<'tm> {
        Term::from_raw(unsafe { simplify(self.inner, term.inner, apply_subs) })
    }

    // ── Model queries ──────────────────────────────────────────────

    /// Get the value of a term in the current model.
    pub fn get_value(&self, term: Term) -> Term<'tm> {
        Term::from_raw(unsafe { get_value(self.inner, term.inner) })
    }

    /// Get the values of multiple terms in the current model.
    pub fn get_values(&self, terms: &[Term]) -> Vec<Term<'tm>> {
        let raw: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        let mut rsize = 0usize;
        let ptr = unsafe { get_values(self.inner, raw.len(), raw.as_ptr(), &mut rsize) };
        (0..rsize)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the domain elements of an uninterpreted sort in the current model.
    pub fn get_model_domain_elements(&self, sort: Sort) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_model_domain_elements(self.inner, sort.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Return `true` if the given variable is a model core symbol.
    pub fn is_model_core_symbol(&self, v: Term) -> bool {
        unsafe { is_model_core_symbol(self.inner, v.inner) }
    }

    /// Get a string representation of the current model.
    pub fn get_model(&self, sorts: &[Sort], consts: &[Term]) -> String {
        let rs: Vec<cvc5_ff_sys::Sort> = sorts.iter().map(|s| s.inner).collect();
        let rt: Vec<cvc5_ff_sys::Term> = consts.iter().map(|t| t.inner).collect();
        unsafe {
            std::ffi::CStr::from_ptr(get_model(
                self.inner,
                rs.len(),
                rs.as_ptr(),
                rt.len(),
                rt.as_ptr(),
            ))
            .to_string_lossy()
            .into_owned()
        }
    }

    /// Block the current model using the given mode.
    pub fn block_model(&mut self, mode: cvc5_ff_sys::BlockModelsMode) {
        unsafe { block_model(self.inner, mode) }
    }

    /// Block the current model values for the given terms.
    pub fn block_model_values(&mut self, terms: &[Term]) {
        let raw: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        unsafe { block_model_values(self.inner, raw.len(), raw.as_ptr()) }
    }

    // ── Declarations ───────────────────────────────────────────────

    /// Declare a function (SMT-LIB `declare-fun`).
    pub fn declare_fun(&mut self, name: &str, domain: &[Sort], codomain: Sort) -> Term<'tm> {
        let c = CString::new(name).unwrap();
        let raw: Vec<cvc5_ff_sys::Sort> = domain.iter().map(|s| s.inner).collect();
        Term::from_raw(unsafe {
            declare_fun(
                self.inner,
                c.as_ptr(),
                raw.len(),
                raw.as_ptr(),
                codomain.inner,
                true,
            )
        })
    }

    /// Declare an uninterpreted sort (SMT-LIB `declare-sort`).
    pub fn declare_sort(&mut self, name: &str, arity: u32) -> Sort<'tm> {
        let c = CString::new(name).unwrap();
        Sort::from_raw(unsafe { declare_sort(self.inner, c.as_ptr(), arity, true) })
    }

    /// Declare a datatype from constructor declarations.
    pub fn declare_dt(&mut self, symbol: &str, ctors: &[DatatypeConstructorDecl]) -> Sort<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::DatatypeConstructorDecl> = ctors.iter().map(|d| d.inner).collect();
        Sort::from_raw(unsafe { declare_dt(self.inner, c.as_ptr(), raw.len(), raw.as_ptr()) })
    }

    // ── Definitions ────────────────────────────────────────────────

    /// Define a function (SMT-LIB `define-fun`).
    pub fn define_fun(
        &mut self,
        symbol: &str,
        vars: &[Term],
        sort: Sort,
        term: Term,
        global: bool,
    ) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::Term> = vars.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            define_fun(
                self.inner,
                c.as_ptr(),
                raw.len(),
                raw.as_ptr(),
                sort.inner,
                term.inner,
                global,
            )
        })
    }

    /// Define a recursive function (SMT-LIB `define-fun-rec`).
    pub fn define_fun_rec(
        &mut self,
        symbol: &str,
        vars: &[Term],
        sort: Sort,
        term: Term,
        global: bool,
    ) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::Term> = vars.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            define_fun_rec(
                self.inner,
                c.as_ptr(),
                raw.len(),
                raw.as_ptr(),
                sort.inner,
                term.inner,
                global,
            )
        })
    }

    /// Define a recursive function from a previously declared constant.
    pub fn define_fun_rec_from_const(
        &mut self,
        fun: Term,
        vars: &[Term],
        term: Term,
        global: bool,
    ) -> Term<'tm> {
        let raw: Vec<cvc5_ff_sys::Term> = vars.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            define_fun_rec_from_const(
                self.inner,
                fun.inner,
                raw.len(),
                raw.as_ptr(),
                term.inner,
                global,
            )
        })
    }

    // ── Scope management ───────────────────────────────────────────

    /// Push `n` assertion scope levels.
    pub fn push(&mut self, n: u32) {
        unsafe { push(self.inner, n) }
    }
    /// Pop `n` assertion scope levels.
    pub fn pop(&mut self, n: u32) {
        unsafe { pop(self.inner, n) }
    }
    /// Remove all assertions and reset the scope.
    pub fn reset_assertions(&mut self) {
        unsafe { reset_assertions(self.inner) }
    }

    // ── Unsat core / assumptions ───────────────────────────────────

    /// Get the unsat core (subset of assertions that are unsatisfiable).
    pub fn get_unsat_core(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_unsat_core(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the lemmas used in the unsat core.
    pub fn get_unsat_core_lemmas(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_unsat_core_lemmas(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the unsat assumptions (subset of assumptions from `check_sat_assuming`).
    pub fn get_unsat_assumptions(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_unsat_assumptions(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    // ── Proofs ─────────────────────────────────────────────────────

    /// Get the proof of unsatisfiability.
    pub fn get_proof(&self, c: cvc5_ff_sys::ProofComponent) -> Vec<Proof<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_proof(self.inner, c, &mut size) };
        (0..size)
            .map(|i| Proof::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Convert a proof to a string in the given format.
    pub fn proof_to_string(
        &self,
        proof: Proof,
        format: cvc5_ff_sys::ProofFormat,
        assertions: &[Term],
        names: &[&str],
    ) -> String {
        let rt: Vec<cvc5_ff_sys::Term> = assertions.iter().map(|t| t.inner).collect();
        let cnames: Vec<CString> = names.iter().map(|n| CString::new(*n).unwrap()).collect();
        let mut ptrs: Vec<*const std::ffi::c_char> = cnames.iter().map(|c| c.as_ptr()).collect();
        unsafe {
            std::ffi::CStr::from_ptr(proof_to_string(
                self.inner,
                proof.inner,
                format,
                rt.len(),
                rt.as_ptr(),
                ptrs.as_mut_ptr(),
            ))
            .to_string_lossy()
            .into_owned()
        }
    }

    // ── Learned literals / difficulty ──────────────────────────────

    /// Get the learned literals of the given type.
    pub fn get_learned_literals(&self, lit_type: cvc5_ff_sys::LearnedLitType) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_learned_literals(self.inner, lit_type, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Get the difficulty of each assertion as `(inputs, values)` pairs.
    pub fn get_difficulty(&self) -> (Vec<Term<'tm>>, Vec<Term<'tm>>) {
        let mut size = 0usize;
        let mut inputs: *mut cvc5_ff_sys::Term = std::ptr::null_mut();
        let mut values: *mut cvc5_ff_sys::Term = std::ptr::null_mut();
        unsafe { get_difficulty(self.inner, &mut size, &mut inputs, &mut values) };
        let i = (0..size)
            .map(|j| Term::from_raw(unsafe { *inputs.add(j) }))
            .collect();
        let v = (0..size)
            .map(|j| Term::from_raw(unsafe { *values.add(j) }))
            .collect();
        (i, v)
    }

    // ── Timeout core ───────────────────────────────────────────────

    /// Get a timeout core: a minimal subset of assertions causing a timeout.
    pub fn get_timeout_core(&mut self) -> (Result<'tm>, Vec<Term<'tm>>) {
        let mut result: cvc5_ff_sys::Result = std::ptr::null_mut();
        let mut size = 0usize;
        let ptr = unsafe { get_timeout_core(self.inner, &mut result, &mut size) };
        let terms = (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect();
        (Result::from_raw(result), terms)
    }

    /// Get a timeout core under the given assumptions.
    pub fn get_timeout_core_assuming(&self, assumptions: &[Term]) -> (Result<'tm>, Vec<Term<'tm>>) {
        let raw: Vec<cvc5_ff_sys::Term> = assumptions.iter().map(|t| t.inner).collect();
        let mut result: cvc5_ff_sys::Result = std::ptr::null_mut();
        let mut rsize = 0usize;
        let ptr = unsafe {
            get_timeout_core_assuming(self.inner, raw.len(), raw.as_ptr(), &mut result, &mut rsize)
        };
        let terms = (0..rsize)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect();
        (Result::from_raw(result), terms)
    }

    // ── Quantifier elimination ─────────────────────────────────────

    /// Perform quantifier elimination on the given formula.
    pub fn get_quantifier_elimination(&self, q: Term) -> Term<'tm> {
        Term::from_raw(unsafe { get_quantifier_elimination(self.inner, q.inner) })
    }

    /// Perform partial quantifier elimination, returning a single disjunct.
    pub fn get_quantifier_elimination_disjunct(&self, q: Term) -> Term<'tm> {
        Term::from_raw(unsafe { get_quantifier_elimination_disjunct(self.inner, q.inner) })
    }

    // ── Separation logic ───────────────────────────────────────────

    /// Declare the heap sorts for separation logic.
    pub fn declare_sep_heap(&mut self, loc: Sort, data: Sort) {
        unsafe { declare_sep_heap(self.inner, loc.inner, data.inner) }
    }

    /// Get the separation logic heap term.
    pub fn get_value_sep_heap(&self) -> Term<'tm> {
        Term::from_raw(unsafe { get_value_sep_heap(self.inner) })
    }

    /// Get the separation logic nil term.
    pub fn get_value_sep_nil(&self) -> Term<'tm> {
        Term::from_raw(unsafe { get_value_sep_nil(self.inner) })
    }

    // ── Pools ──────────────────────────────────────────────────────

    /// Declare a term pool with the given initial values.
    pub fn declare_pool(&mut self, symbol: &str, sort: Sort, init_value: &[Term]) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::Term> = init_value.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            declare_pool(self.inner, c.as_ptr(), sort.inner, raw.len(), raw.as_ptr())
        })
    }

    // ── Interpolation ──────────────────────────────────────────────

    /// Compute an interpolant for the given conjecture.
    ///
    /// Returns `None` if no interpolant exists.
    pub fn get_interpolant(&self, conj: Term) -> Option<Term<'tm>> {
        let raw = unsafe { get_interpolant(self.inner, conj.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Compute an interpolant constrained by the given grammar.
    ///
    /// Returns `None` if no interpolant exists.
    pub fn get_interpolant_with_grammar(&self, conj: Term, grammar: &Grammar) -> Option<Term<'tm>> {
        let raw = unsafe { get_interpolant_with_grammar(self.inner, conj.inner, grammar.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Get the next interpolant (after a previous `get_interpolant` call).
    ///
    /// Returns `None` if no further interpolant can be found.
    pub fn get_interpolant_next(&self) -> Option<Term<'tm>> {
        let raw = unsafe { get_interpolant_next(self.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    // ── Abduction ──────────────────────────────────────────────────

    /// Compute an abduct for the given conjecture.
    ///
    /// Returns `None` if no abduct can be found.
    pub fn get_abduct(&self, conj: Term) -> Option<Term<'tm>> {
        let raw = unsafe { get_abduct(self.inner, conj.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Compute an abduct constrained by the given grammar.
    ///
    /// Returns `None` if no abduct can be found.
    pub fn get_abduct_with_grammar(&self, conj: Term, grammar: &Grammar) -> Option<Term<'tm>> {
        let raw = unsafe { get_abduct_with_grammar(self.inner, conj.inner, grammar.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Get the next abduct (after a previous `get_abduct` call).
    ///
    /// Returns `None` if no further abduct can be found.
    pub fn get_abduct_next(&self) -> Option<Term<'tm>> {
        let raw = unsafe { get_abduct_next(self.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    // ── Instantiations ─────────────────────────────────────────────

    /// Get a string representation of all quantifier instantiations.
    pub fn get_instantiations(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(get_instantiations(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    // ── SyGuS ──────────────────────────────────────────────────────

    /// Declare a SyGuS variable.
    pub fn declare_sygus_var(&mut self, symbol: &str, sort: Sort) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        Term::from_raw(unsafe { declare_sygus_var(self.inner, c.as_ptr(), sort.inner) })
    }

    /// Create a SyGuS grammar from bound variables and non-terminal symbols.
    pub fn mk_grammar(&self, bound_vars: &[Term], symbols: &[Term]) -> Grammar<'tm> {
        let bv: Vec<cvc5_ff_sys::Term> = bound_vars.iter().map(|t| t.inner).collect();
        let sy: Vec<cvc5_ff_sys::Term> = symbols.iter().map(|t| t.inner).collect();
        Grammar::from_raw(unsafe {
            mk_grammar(self.inner, bv.len(), bv.as_ptr(), sy.len(), sy.as_ptr())
        })
    }

    /// Declare a function to synthesize (SyGuS `synth-fun`).
    pub fn synth_fun(&mut self, symbol: &str, bound_vars: &[Term], sort: Sort) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::Term> = bound_vars.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            synth_fun(self.inner, c.as_ptr(), raw.len(), raw.as_ptr(), sort.inner)
        })
    }

    /// Declare a function to synthesize with a grammar constraint.
    pub fn synth_fun_with_grammar(
        &mut self,
        symbol: &str,
        bound_vars: &[Term],
        sort: Sort,
        grammar: &Grammar,
    ) -> Term<'tm> {
        let c = CString::new(symbol).unwrap();
        let raw: Vec<cvc5_ff_sys::Term> = bound_vars.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            synth_fun_with_grammar(
                self.inner,
                c.as_ptr(),
                raw.len(),
                raw.as_ptr(),
                sort.inner,
                grammar.inner,
            )
        })
    }

    /// Add a SyGuS constraint.
    pub fn add_sygus_constraint(&mut self, term: Term) {
        unsafe { add_sygus_constraint(self.inner, term.inner) }
    }

    /// Get the list of SyGuS constraints.
    pub fn get_sygus_constraints(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_sygus_constraints(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Add a SyGuS assumption.
    pub fn add_sygus_assume(&mut self, term: Term) {
        unsafe { add_sygus_assume(self.inner, term.inner) }
    }

    /// Get the list of SyGuS assumptions.
    pub fn get_sygus_assumptions(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { get_sygus_assumptions(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Add a SyGuS invariant constraint.
    pub fn add_sygus_inv_constraint(&mut self, inv: Term, pre: Term, trans: Term, post: Term) {
        unsafe {
            add_sygus_inv_constraint(self.inner, inv.inner, pre.inner, trans.inner, post.inner)
        }
    }

    /// Check for a synthesis solution.
    pub fn check_synth(&mut self) -> SynthResult<'tm> {
        SynthResult::from_raw(unsafe { check_synth(self.inner) })
    }

    /// Get the next synthesis solution.
    pub fn check_synth_next(&mut self) -> SynthResult<'tm> {
        SynthResult::from_raw(unsafe { check_synth_next(self.inner) })
    }

    /// Get the synthesis solution for a given function-to-synthesize term.
    pub fn get_synth_solution(&self, term: Term) -> Term<'tm> {
        Term::from_raw(unsafe { get_synth_solution(self.inner, term.inner) })
    }

    /// Get synthesis solutions for multiple function-to-synthesize terms.
    pub fn get_synth_solutions(&self, terms: &[Term]) -> Vec<Term<'tm>> {
        let raw: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        let ptr = unsafe { get_synth_solutions(self.inner, raw.len(), raw.as_ptr()) };
        (0..terms.len())
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Find a synthesis target of the given type.
    ///
    /// Returns `None` if the call failed.
    pub fn find_synth(&self, target: cvc5_ff_sys::FindSynthTarget) -> Option<Term<'tm>> {
        let raw = unsafe { find_synth(self.inner, target) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Find a synthesis target constrained by the given grammar.
    ///
    /// Returns `None` if the call failed.
    pub fn find_synth_with_grammar(
        &mut self,
        target: cvc5_ff_sys::FindSynthTarget,
        grammar: &Grammar,
    ) -> Option<Term<'tm>> {
        let raw = unsafe { find_synth_with_grammar(self.inner, target, grammar.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    /// Get the next synthesis target.
    ///
    /// Returns `None` if the call failed.
    pub fn find_synth_next(&self) -> Option<Term<'tm>> {
        let raw = unsafe { find_synth_next(self.inner) };
        (!raw.is_null()).then(|| Term::from_raw(raw))
    }

    // ── Mutually recursive definitions ─────────────────────────────

    /// Define mutually recursive functions.
    pub fn define_funs_rec(
        &mut self,
        funs: &[Term],
        vars: &[&[Term]],
        terms: &[Term],
        global: bool,
    ) {
        let rf: Vec<cvc5_ff_sys::Term> = funs.iter().map(|t| t.inner).collect();
        let mut nvars: Vec<usize> = vars.iter().map(|v| v.len()).collect();
        let raw_vars: Vec<Vec<cvc5_ff_sys::Term>> = vars
            .iter()
            .map(|v| v.iter().map(|t| t.inner).collect())
            .collect();
        let mut var_ptrs: Vec<*const cvc5_ff_sys::Term> =
            raw_vars.iter().map(|v| v.as_ptr()).collect();
        let rt: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        unsafe {
            define_funs_rec(
                self.inner,
                rf.len(),
                rf.as_ptr(),
                nvars.as_mut_ptr(),
                var_ptrs.as_mut_ptr(),
                rt.as_ptr(),
                global,
            )
        }
    }

    // ── Output ─────────────────────────────────────────────────────

    /// Redirect solver output for the given tag to a file.
    pub fn get_output(&self, tag: &str, filename: &str) {
        let t = CString::new(tag).unwrap();
        let f = CString::new(filename).unwrap();
        unsafe { get_output(self.inner, t.as_ptr(), f.as_ptr()) }
    }

    /// Close a previously opened output file.
    pub fn close_output(&self, filename: &str) {
        let f = CString::new(filename).unwrap();
        unsafe { close_output(self.inner, f.as_ptr()) }
    }

    /// Print statistics to the given file descriptor (async-signal-safe).
    pub fn print_stats_safe(&self, fd: i32) {
        unsafe { print_stats_safe(self.inner, fd) }
    }

    // ── Statistics / output ────────────────────────────────────────

    /// Return `true` if the given output tag is enabled.
    pub fn is_output_on(&self, tag: &str) -> bool {
        let c = CString::new(tag).unwrap();
        unsafe { is_output_on(self.inner, c.as_ptr()) }
    }

    /// Get the solver statistics.
    pub fn get_statistics(&self) -> Statistics {
        Statistics::from_raw(unsafe { get_statistics(self.inner) })
    }

    /**
    Get detailed information about a solver option.
     */
    pub fn get_option_info(&mut self, option: &str) -> OptionInfo<'_> {
        let c = CString::new(option).unwrap();
        let mut info: cvc5_ff_sys::OptionInfo = unsafe { std::mem::zeroed() };
        unsafe { get_option_info(self.inner, c.as_ptr(), &mut info) };
        OptionInfo {
            inner: info,
            _phantom: PhantomData,
        }
    }

    // ── Plugin ─────────────────────────────────────────────────────

    /// Add a plugin to the solver.
    pub fn add_plugin(&mut self, plugin: &mut cvc5_ff_sys::Plugin) {
        unsafe { add_plugin(self.inner, plugin) }
    }

    /// Get the cvc5 version string.
    pub fn version(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(get_version(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }
}

impl Drop for Solver<'_> {
    fn drop(&mut self) {
        unsafe { delete(self.inner) }
    }
}
