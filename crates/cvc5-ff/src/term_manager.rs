use cvc5_ff_sys::*;
use std::ffi::CString;
use std::rc::Rc;

use crate::{DatatypeConstructorDecl, DatatypeDecl, Op, Sort, Statistics, Term};

struct RawTermManager(*mut cvc5_ff_sys::TermManager);

impl RawTermManager {
    fn new() -> Self {
        Self(unsafe { term_manager_new() })
    }
}

impl Drop for RawTermManager {
    fn drop(&mut self) {
        unsafe { term_manager_delete(self.0) };
    }
}

/// Manages creation of sorts, terms, and operators.
#[derive(Clone)]
pub struct TermManager {
    inner: Rc<RawTermManager>,
}

impl TermManager {
    /// Create a new term manager.
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RawTermManager::new()),
        }
    }

    /// Raw pointer for read-only access.
    pub(crate) fn ptr(&self) -> *mut cvc5_ff_sys::TermManager {
        self.inner.0
    }

    // ── Sort creation ──────────────────────────────────────────────

    /// Get the Boolean sort.
    pub fn boolean_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_boolean_sort(self.ptr()) })
    }
    /// Get the Integer sort.
    pub fn integer_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_integer_sort(self.ptr()) })
    }
    /// Get the Real sort.
    pub fn real_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_real_sort(self.ptr()) })
    }
    /// Get the String sort.
    pub fn string_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_string_sort(self.ptr()) })
    }
    /// Get the RegExp sort.
    pub fn regexp_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_regexp_sort(self.ptr()) })
    }
    /// Get the rounding mode sort.
    pub fn rm_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { get_rm_sort(self.ptr()) })
    }

    /// Create an array sort with the given index and element sorts.
    pub fn mk_array_sort(&self, index: Sort, elem: Sort) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_array_sort(self.ptr(), index.inner, elem.inner) })
    }

    /// Create a bit-vector sort of the given bit-width.
    pub fn mk_bv_sort(&self, size: u32) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_bv_sort(self.ptr(), size) })
    }

    /// Create a floating-point sort with the given exponent and significand sizes.
    pub fn mk_fp_sort(&self, exp: u32, sig: u32) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_fp_sort(self.ptr(), exp, sig) })
    }

    /// Create a finite field sort of the given size (modulus) in the given base.
    pub fn mk_ff_sort(&self, size: &str, base: u32) -> Sort<'_> {
        let c = CString::new(size).unwrap();
        Sort::from_raw(unsafe { mk_ff_sort(self.ptr(), c.as_ptr(), base) })
    }

    /// Create a datatype sort from a datatype declaration.
    pub fn mk_dt_sort(&self, decl: &DatatypeDecl) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_dt_sort(self.ptr(), decl.inner) })
    }

    /// Create mutually recursive datatype sorts from declarations.
    pub fn mk_dt_sorts(&self, decls: &[DatatypeDecl]) -> Vec<Sort<'_>> {
        let raw: Vec<cvc5_ff_sys::DatatypeDecl> = decls.iter().map(|d| d.inner).collect();
        let ptr = unsafe { mk_dt_sorts(self.ptr(), raw.len(), raw.as_ptr()) };
        (0..decls.len())
            .map(|i| Sort::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Create a function sort with the given domain and codomain sorts.
    pub fn mk_fun_sort(&self, domain: &[Sort], codomain: Sort) -> Sort<'_> {
        let raw: Vec<cvc5_ff_sys::Sort> = domain.iter().map(|s| s.inner).collect();
        Sort::from_raw(unsafe { mk_fun_sort(self.ptr(), raw.len(), raw.as_ptr(), codomain.inner) })
    }

    /// Create a sort parameter with the given symbol.
    pub fn mk_param_sort(&self, symbol: &str) -> Sort<'_> {
        let c = CString::new(symbol).unwrap();
        Sort::from_raw(unsafe { mk_param_sort(self.ptr(), c.as_ptr()) })
    }

    /// Create a predicate sort (function sort with Boolean codomain).
    pub fn mk_predicate_sort(&self, sorts: &[Sort]) -> Sort<'_> {
        let raw: Vec<cvc5_ff_sys::Sort> = sorts.iter().map(|s| s.inner).collect();
        Sort::from_raw(unsafe { mk_predicate_sort(self.ptr(), raw.len(), raw.as_ptr()) })
    }

    /// Create a record sort with the given field names and sorts.
    pub fn mk_record_sort(&self, names: &[&str], sorts: &[Sort]) -> Sort<'_> {
        let cnames: Vec<CString> = names.iter().map(|n| CString::new(*n).unwrap()).collect();
        let mut ptrs: Vec<*const std::ffi::c_char> = cnames.iter().map(|c| c.as_ptr()).collect();
        let raw: Vec<cvc5_ff_sys::Sort> = sorts.iter().map(|s| s.inner).collect();
        Sort::from_raw(unsafe {
            mk_record_sort(self.ptr(), raw.len(), ptrs.as_mut_ptr(), raw.as_ptr())
        })
    }

    /// Create a set sort with the given element sort.
    pub fn mk_set_sort(&self, elem: Sort) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_set_sort(self.ptr(), elem.inner) })
    }

    /// Create a bag sort with the given element sort.
    pub fn mk_bag_sort(&self, elem: Sort) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_bag_sort(self.ptr(), elem.inner) })
    }

    /// Create a sequence sort with the given element sort.
    pub fn mk_sequence_sort(&self, elem: Sort) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_sequence_sort(self.ptr(), elem.inner) })
    }

    /// Create an abstract sort of the given sort kind.
    pub fn mk_abstract_sort(&self, k: cvc5_ff_sys::SortKind) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_abstract_sort(self.ptr(), k) })
    }

    /// Create a named uninterpreted sort.
    pub fn mk_uninterpreted_sort(&self, name: &str) -> Sort<'_> {
        let c = CString::new(name).unwrap();
        Sort::from_raw(unsafe { mk_uninterpreted_sort(self.ptr(), c.as_ptr()) })
    }

    /// Create an anonymous uninterpreted sort (no symbol).
    pub fn mk_anonymous_uninterpreted_sort(&self) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_uninterpreted_sort(self.ptr(), std::ptr::null()) })
    }

    /// Create an unresolved datatype sort placeholder for mutual recursion.
    pub fn mk_unresolved_dt_sort(&self, symbol: &str, arity: usize) -> Sort<'_> {
        let c = CString::new(symbol).unwrap();
        Sort::from_raw(unsafe { mk_unresolved_dt_sort(self.ptr(), c.as_ptr(), arity) })
    }

    /// Create an uninterpreted sort constructor of the given arity.
    pub fn mk_uninterpreted_sort_constructor_sort(&self, arity: usize, symbol: &str) -> Sort<'_> {
        let c = CString::new(symbol).unwrap();
        Sort::from_raw(unsafe {
            mk_uninterpreted_sort_constructor_sort(self.ptr(), arity, c.as_ptr())
        })
    }

    /// Create an anonymous uninterpreted sort constructor of the given arity.
    pub fn mk_anonymous_uninterpreted_sort_constructor_sort(&self, arity: usize) -> Sort<'_> {
        Sort::from_raw(unsafe {
            mk_uninterpreted_sort_constructor_sort(self.ptr(), arity, std::ptr::null())
        })
    }

    /// Create a tuple sort with the given element sorts.
    pub fn mk_tuple_sort(&self, sorts: &[Sort]) -> Sort<'_> {
        let raw: Vec<cvc5_ff_sys::Sort> = sorts.iter().map(|s| s.inner).collect();
        Sort::from_raw(unsafe { mk_tuple_sort(self.ptr(), raw.len(), raw.as_ptr()) })
    }

    /// Create a nullable sort wrapping the given sort.
    pub fn mk_nullable_sort(&self, sort: Sort) -> Sort<'_> {
        Sort::from_raw(unsafe { mk_nullable_sort(self.ptr(), sort.inner) })
    }

    // ── Operator creation ──────────────────────────────────────────

    /// Create an indexed operator with the given kind and integer indices.
    pub fn mk_op(&self, kind: cvc5_ff_sys::Kind, indices: &[u32]) -> Op<'_> {
        Op::from_raw(unsafe { mk_op(self.ptr(), kind, indices.len(), indices.as_ptr()) })
    }

    /// Create an indexed operator with the given kind and string argument.
    pub fn mk_op_from_str(&self, kind: cvc5_ff_sys::Kind, arg: &str) -> Op<'_> {
        let c = CString::new(arg).unwrap();
        Op::from_raw(unsafe { mk_op_from_str(self.ptr(), kind, c.as_ptr()) })
    }

    // ── Term creation ──────────────────────────────────────────────

    /// Create a term with the given kind and children.
    pub fn mk_term(&self, kind: cvc5_ff_sys::Kind, children: &[Term]) -> Term<'_> {
        let raw: Vec<cvc5_ff_sys::Term> = children.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe { mk_term(self.ptr(), kind, raw.len(), raw.as_ptr()) })
    }

    /// Create a term from an operator and children.
    pub fn mk_term_from_op(&self, op: Op, children: &[Term]) -> Term<'_> {
        let raw: Vec<cvc5_ff_sys::Term> = children.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe { mk_term_from_op(self.ptr(), op.inner, raw.len(), raw.as_ptr()) })
    }

    /// Create a tuple term from the given elements.
    pub fn mk_tuple(&self, terms: &[Term]) -> Term<'_> {
        let raw: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe { mk_tuple(self.ptr(), raw.len(), raw.as_ptr()) })
    }

    /// Create a nullable term wrapping the given value.
    pub fn mk_nullable_some(&self, term: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_nullable_some(self.ptr(), term.inner) })
    }

    /// Extract the value from a nullable term.
    pub fn mk_nullable_val(&self, term: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_nullable_val(self.ptr(), term.inner) })
    }

    /// Create a term testing whether a nullable is null.
    pub fn mk_nullable_is_null(&self, term: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_nullable_is_null(self.ptr(), term.inner) })
    }

    /// Create a term testing whether a nullable has a value.
    pub fn mk_nullable_is_some(&self, term: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_nullable_is_some(self.ptr(), term.inner) })
    }

    /// Create a null nullable term of the given sort.
    pub fn mk_nullable_null(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_nullable_null(self.ptr(), sort.inner) })
    }

    /// Lift an operator over nullable arguments.
    pub fn mk_nullable_lift(&self, kind: cvc5_ff_sys::Kind, args: &[Term]) -> Term<'_> {
        let raw: Vec<cvc5_ff_sys::Term> = args.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe { mk_nullable_lift(self.ptr(), kind, raw.len(), raw.as_ptr()) })
    }

    /// Create a Skolem term with the given identifier and indices.
    pub fn mk_skolem(&self, id: cvc5_ff_sys::SkolemId, indices: &[Term]) -> Term<'_> {
        let raw: Vec<cvc5_ff_sys::Term> = indices.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe { mk_skolem(self.ptr(), id, raw.len(), raw.as_ptr()) })
    }

    /// Get the number of indices expected for the given Skolem identifier.
    pub fn get_num_idxs_for_skolem_id(&self, id: cvc5_ff_sys::SkolemId) -> usize {
        unsafe { get_num_idxs_for_skolem_id(self.ptr(), id) }
    }

    // ── Constants ──────────────────────────────────────────────────

    /// Create the Boolean constant `true`.
    pub fn mk_true(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_true(self.ptr()) })
    }
    /// Create the Boolean constant `false`.
    pub fn mk_false(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_false(self.ptr()) })
    }
    /// Create a Boolean constant from a Rust `bool`.
    pub fn mk_boolean(&self, val: bool) -> Term<'_> {
        Term::from_raw(unsafe { mk_boolean(self.ptr(), val) })
    }
    /// Create the constant pi.
    pub fn mk_pi(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_pi(self.ptr()) })
    }

    /// Create an integer constant from an `i64`.
    pub fn mk_integer(&self, val: i64) -> Term<'_> {
        Term::from_raw(unsafe { mk_integer_int64(self.ptr(), val) })
    }

    /// Create an integer constant from a decimal string.
    pub fn mk_integer_from_str(&self, s: &str) -> Term<'_> {
        let c = CString::new(s).unwrap();
        Term::from_raw(unsafe { mk_integer(self.ptr(), c.as_ptr()) })
    }

    /// Create a real constant from an `i64`.
    pub fn mk_real(&self, val: i64) -> Term<'_> {
        Term::from_raw(unsafe { mk_real_int64(self.ptr(), val) })
    }

    /// Create a real constant from a decimal string.
    pub fn mk_real_from_str(&self, s: &str) -> Term<'_> {
        let c = CString::new(s).unwrap();
        Term::from_raw(unsafe { mk_real(self.ptr(), c.as_ptr()) })
    }

    /// Create a real constant from a numerator and denominator.
    pub fn mk_real_from_rational(&self, num: i64, den: i64) -> Term<'_> {
        Term::from_raw(unsafe { mk_real_num_den(self.ptr(), num, den) })
    }

    /// Create the regular expression that matches everything (`re.all`).
    pub fn mk_regexp_all(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_regexp_all(self.ptr()) })
    }
    /// Create the regular expression that matches any single character.
    pub fn mk_regexp_allchar(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_regexp_allchar(self.ptr()) })
    }
    /// Create the regular expression that matches nothing (`re.none`).
    pub fn mk_regexp_none(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_regexp_none(self.ptr()) })
    }

    /// Create an empty set of the given sort.
    pub fn mk_empty_set(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_empty_set(self.ptr(), sort.inner) })
    }

    /// Create an empty bag of the given sort.
    pub fn mk_empty_bag(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_empty_bag(self.ptr(), sort.inner) })
    }

    /// Create the separation logic empty heap constraint.
    pub fn mk_sep_emp(&self) -> Term<'_> {
        Term::from_raw(unsafe { mk_sep_emp(self.ptr()) })
    }

    /// Create the separation logic nil term of the given sort.
    pub fn mk_sep_nil(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_sep_nil(self.ptr(), sort.inner) })
    }

    /// Create a string constant. If `use_esc_seq` is true, process escape sequences.
    pub fn mk_string(&self, s: &str, use_esc_seq: bool) -> Term<'_> {
        let c = CString::new(s).unwrap();
        Term::from_raw(unsafe { mk_string(self.ptr(), c.as_ptr(), use_esc_seq) })
    }

    /// Create an empty sequence of the given element sort.
    pub fn mk_empty_sequence(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_empty_sequence(self.ptr(), sort.inner) })
    }

    /// Create the universe set of the given sort.
    pub fn mk_universe_set(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_universe_set(self.ptr(), sort.inner) })
    }

    /// Create a bit-vector constant of the given size and value.
    pub fn mk_bv(&self, size: u32, val: u64) -> Term<'_> {
        Term::from_raw(unsafe { mk_bv_uint64(self.ptr(), size, val) })
    }

    /// Create a bit-vector constant from a string in the given base (2, 10, or 16).
    pub fn mk_bv_from_str(&self, size: u32, s: &str, base: u32) -> Term<'_> {
        let c = CString::new(s).unwrap();
        Term::from_raw(unsafe { mk_bv(self.ptr(), size, c.as_ptr(), base) })
    }

    /// Create a finite field element from a string value in the given base.
    pub fn mk_ff_elem(&self, value: &str, sort: Sort, base: u32) -> Term<'_> {
        let c = CString::new(value).unwrap();
        Term::from_raw(unsafe { mk_ff_elem(self.ptr(), c.as_ptr(), sort.inner, base) })
    }

    /// Create a constant array where every element is `val`.
    pub fn mk_const_array(&self, sort: Sort, val: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_const_array(self.ptr(), sort.inner, val.inner) })
    }

    /// Create a positive infinity floating-point constant.
    pub fn mk_fp_pos_inf(&self, exp: u32, sig: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_pos_inf(self.ptr(), exp, sig) })
    }

    /// Create a negative infinity floating-point constant.
    pub fn mk_fp_neg_inf(&self, exp: u32, sig: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_neg_inf(self.ptr(), exp, sig) })
    }

    /// Create a NaN floating-point constant.
    pub fn mk_fp_nan(&self, exp: u32, sig: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_nan(self.ptr(), exp, sig) })
    }

    /// Create a positive zero floating-point constant.
    pub fn mk_fp_pos_zero(&self, exp: u32, sig: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_pos_zero(self.ptr(), exp, sig) })
    }

    /// Create a negative zero floating-point constant.
    pub fn mk_fp_neg_zero(&self, exp: u32, sig: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_neg_zero(self.ptr(), exp, sig) })
    }

    /// Create a rounding mode constant.
    pub fn mk_rm(&self, rm: cvc5_ff_sys::RoundingMode) -> Term<'_> {
        Term::from_raw(unsafe { mk_rm(self.ptr(), rm) })
    }

    /// Create a floating-point constant from a bit-vector value.
    pub fn mk_fp(&self, exp: u32, sig: u32, val: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp(self.ptr(), exp, sig, val.inner) })
    }

    /// Create a floating-point constant from IEEE 754 sign, exponent, and significand bit-vectors.
    pub fn mk_fp_from_ieee(&self, sign: Term, exp: Term, sig: Term) -> Term<'_> {
        Term::from_raw(unsafe { mk_fp_from_ieee(self.ptr(), sign.inner, exp.inner, sig.inner) })
    }

    /// Create a cardinality constraint on the given sort.
    pub fn mk_cardinality_constraint(&self, sort: Sort, upper_bound: u32) -> Term<'_> {
        Term::from_raw(unsafe { mk_cardinality_constraint(self.ptr(), sort.inner, upper_bound) })
    }

    // ── Variables ──────────────────────────────────────────────────

    /// Create a named constant (free variable) of the given sort.
    pub fn mk_const(&self, sort: Sort, name: &str) -> Term<'_> {
        let c = CString::new(name).unwrap();
        Term::from_raw(unsafe { mk_const(self.ptr(), sort.inner, c.as_ptr()) })
    }

    /// Create an anonymous constant (free variable) of the given sort.
    pub fn mk_anonymous_const(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_const(self.ptr(), sort.inner, std::ptr::null()) })
    }

    /// Create a bound variable of the given sort.
    pub fn mk_var(&self, sort: Sort, name: &str) -> Term<'_> {
        let c = CString::new(name).unwrap();
        Term::from_raw(unsafe { mk_var(self.ptr(), sort.inner, c.as_ptr()) })
    }

    /// Create an anonymous bound variable of the given sort.
    pub fn mk_anonymous_var(&self, sort: Sort) -> Term<'_> {
        Term::from_raw(unsafe { mk_var(self.ptr(), sort.inner, std::ptr::null()) })
    }

    // ── Datatype declarations ──────────────────────────────────────

    /// Create a datatype constructor declaration with the given name.
    pub fn mk_dt_cons_decl(&self, name: &str) -> DatatypeConstructorDecl<'_> {
        let c = CString::new(name).unwrap();
        DatatypeConstructorDecl::from_raw(unsafe { mk_dt_cons_decl(self.ptr(), c.as_ptr()) })
    }

    /// Create a datatype declaration. Set `is_codt` to `true` for codatatypes.
    pub fn mk_dt_decl(&self, name: &str, is_codt: bool) -> DatatypeDecl<'_> {
        let c = CString::new(name).unwrap();
        DatatypeDecl::from_raw(unsafe { mk_dt_decl(self.ptr(), c.as_ptr(), is_codt) })
    }

    /// Create a parametric datatype declaration with sort parameters.
    pub fn mk_dt_decl_with_params(
        &self,
        name: &str,
        params: &[Sort],
        is_codt: bool,
    ) -> DatatypeDecl<'_> {
        let c = CString::new(name).unwrap();
        let raw: Vec<cvc5_ff_sys::Sort> = params.iter().map(|s| s.inner).collect();
        DatatypeDecl::from_raw(unsafe {
            mk_dt_decl_with_params(self.ptr(), c.as_ptr(), raw.len(), raw.as_ptr(), is_codt)
        })
    }

    /// Create a string constant from a null-terminated `wchar_t` array.
    pub fn mk_string_from_wchar(&self, s: &[wchar_t]) -> Term<'_> {
        Term::from_raw(unsafe { mk_string_from_wchar(self.ptr(), s.as_ptr()) })
    }

    /// Create a string constant from a null-terminated `char32_t` array.
    pub fn mk_string_from_char32(&self, s: &[char32_t]) -> Term<'_> {
        Term::from_raw(unsafe { mk_string_from_char32(self.ptr(), s.as_ptr()) })
    }

    /// Get the term manager statistics.
    pub fn get_statistics(&self) -> Statistics {
        Statistics::from_raw(unsafe { term_manager_get_statistics(self.ptr()) })
    }

    /// Print term manager statistics to the given file descriptor (async-signal-safe).
    pub fn print_stats_safe(&self, fd: i32) {
        unsafe { term_manager_print_stats_safe(self.ptr(), fd) }
    }
}

impl Default for TermManager {
    fn default() -> Self {
        Self::new()
    }
}
