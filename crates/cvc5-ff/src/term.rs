use cvc5_ff_sys::*;
use std::fmt;
use std::marker::PhantomData;

use crate::{Op, Sort};

/// A cvc5 term (expression or formula).
///
/// Terms are the main building blocks for assertions, queries, and models.
/// The lifetime `'tm` ties this term to the [`TermManager`](crate::TermManager)
/// that created it, preventing use-after-free.
pub struct Term<'tm> {
    pub(crate) inner: cvc5_ff_sys::Term,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Term<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { term_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Term<'_> {
    fn drop(&mut self) {
        unsafe { term_release(self.inner) }
    }
}

impl<'tm> Term<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Term) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Get the kind of this term.
    pub fn kind(&self) -> cvc5_ff_sys::Kind {
        unsafe { term_get_kind(self.inner) }
    }

    /// Create a copy of this term (increments the internal reference count).
    pub fn copy(&self) -> Term<'tm> {
        Term::from_raw(unsafe { term_copy(self.inner) })
    }

    /// Check disequality with another term.
    pub fn is_disequal(&self, other: &Term) -> bool {
        unsafe { term_is_disequal(self.inner, other.inner) }
    }

    /// Get the sort of this term.
    pub fn sort(&self) -> Sort<'tm> {
        Sort::from_raw(unsafe { term_get_sort(self.inner) })
    }

    /// Get the unique identifier of this term.
    pub fn id(&self) -> u64 {
        unsafe { term_get_id(self.inner) }
    }

    /// Get the number of children of this term.
    pub fn num_children(&self) -> usize {
        unsafe { term_get_num_children(self.inner) }
    }

    /// Get the child at the given index.
    pub fn child(&self, index: usize) -> Term<'tm> {
        Term::from_raw(unsafe { term_get_child(self.inner, index) })
    }

    /// Return `true` if this term has a symbol (name).
    pub fn has_symbol(&self) -> bool {
        unsafe { term_has_symbol(self.inner) }
    }

    /// Get the symbol (name) of this term.
    pub fn symbol(&self) -> &str {
        unsafe {
            let s = term_get_symbol(self.inner);
            std::ffi::CStr::from_ptr(s).to_str().unwrap_or("")
        }
    }

    /// Return `true` if this term has an associated operator.
    pub fn has_op(&self) -> bool {
        unsafe { term_has_op(self.inner) }
    }

    /// Get the operator associated with this term.
    pub fn op(&self) -> Op<'tm> {
        Op::from_raw(unsafe { term_get_op(self.inner) })
    }

    /// Substitute `t` with `replacement` in this term.
    pub fn substitute_term(&self, t: Term, replacement: Term) -> Term<'tm> {
        Term::from_raw(unsafe { term_substitute_term(self.inner, t.inner, replacement.inner) })
    }

    /// Simultaneously substitute `terms` with `replacements` in this term.
    pub fn substitute_terms(&self, terms: &[Term], replacements: &[Term]) -> Term<'tm> {
        let t: Vec<cvc5_ff_sys::Term> = terms.iter().map(|t| t.inner).collect();
        let r: Vec<cvc5_ff_sys::Term> = replacements.iter().map(|t| t.inner).collect();
        Term::from_raw(unsafe {
            term_substitute_terms(self.inner, t.len(), t.as_ptr(), r.as_ptr())
        })
    }

    /// Get the sign of a real or integer value: -1, 0, or 1.
    pub fn real_or_integer_value_sign(&self) -> i32 {
        unsafe { term_get_real_or_integer_value_sign(self.inner) }
    }

    /// Return `true` if this term is a Boolean value.
    pub fn is_boolean_value(&self) -> bool {
        unsafe { term_is_boolean_value(self.inner) }
    }
    /// Get the Boolean value of this term.
    pub fn boolean_value(&self) -> bool {
        unsafe { term_get_boolean_value(self.inner) }
    }

    /// Return `true` if this term is a 32-bit signed integer value.
    pub fn is_int32_value(&self) -> bool {
        unsafe { term_is_int32_value(self.inner) }
    }
    /// Get the 32-bit signed integer value.
    pub fn int32_value(&self) -> i32 {
        unsafe { term_get_int32_value(self.inner) }
    }

    /// Return `true` if this term is a 32-bit unsigned integer value.
    pub fn is_uint32_value(&self) -> bool {
        unsafe { term_is_uint32_value(self.inner) }
    }
    /// Get the 32-bit unsigned integer value.
    pub fn uint32_value(&self) -> u32 {
        unsafe { term_get_uint32_value(self.inner) }
    }

    /// Return `true` if this term is a 64-bit signed integer value.
    pub fn is_int64_value(&self) -> bool {
        unsafe { term_is_int64_value(self.inner) }
    }
    /// Get the 64-bit signed integer value.
    pub fn int64_value(&self) -> i64 {
        unsafe { term_get_int64_value(self.inner) }
    }

    /// Return `true` if this term is a 64-bit unsigned integer value.
    pub fn is_uint64_value(&self) -> bool {
        unsafe { term_is_uint64_value(self.inner) }
    }
    /// Get the 64-bit unsigned integer value.
    pub fn uint64_value(&self) -> u64 {
        unsafe { term_get_uint64_value(self.inner) }
    }

    /// Return `true` if this term is an arbitrary-precision integer value.
    pub fn is_integer_value(&self) -> bool {
        unsafe { term_is_integer_value(self.inner) }
    }
    /// Get the integer value as a decimal string.
    pub fn integer_value(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(term_get_integer_value(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return `true` if this term is a string value.
    pub fn is_string_value(&self) -> bool {
        unsafe { term_is_string_value(self.inner) }
    }
    /// Get the string value as a sequence of `wchar_t` code points.
    pub fn string_value(&self) -> Vec<char32_t> {
        let ptr = unsafe { term_get_string_value(self.inner) };
        let mut v = Vec::new();
        let mut i = 0;
        loop {
            let c = unsafe { *ptr.add(i) };
            if c == 0 {
                break;
            }
            v.push(c as char32_t);
            i += 1;
        }
        v
    }
    /// Get the string value as a sequence of Unicode code points (`char32_t`).
    pub fn u32string_value(&self) -> Vec<char32_t> {
        let ptr = unsafe { term_get_u32string_value(self.inner) };
        let mut v = Vec::new();
        let mut i = 0;
        loop {
            let c = unsafe { *ptr.add(i) };
            if c == 0 {
                break;
            }
            v.push(c);
            i += 1;
        }
        v
    }

    /// Return `true` if this term is a rational value representable as 32-bit `(num, den)`.
    pub fn is_real32_value(&self) -> bool {
        unsafe { term_is_real32_value(self.inner) }
    }
    /// Get the rational value as `(numerator, denominator)` with 32-bit components.
    pub fn real32_value(&self) -> (i32, u32) {
        let (mut num, mut den) = (0i32, 0u32);
        unsafe { term_get_real32_value(self.inner, &mut num, &mut den) };
        (num, den)
    }

    /// Return `true` if this term is a rational value representable as 64-bit `(num, den)`.
    pub fn is_real64_value(&self) -> bool {
        unsafe { term_is_real64_value(self.inner) }
    }
    /// Get the rational value as `(numerator, denominator)` with 64-bit components.
    pub fn real64_value(&self) -> (i64, u64) {
        let (mut num, mut den) = (0i64, 0u64);
        unsafe { term_get_real64_value(self.inner, &mut num, &mut den) };
        (num, den)
    }

    /// Return `true` if this term is an arbitrary-precision real value.
    pub fn is_real_value(&self) -> bool {
        unsafe { term_is_real_value(self.inner) }
    }
    /// Get the real value as a decimal string (e.g. `"1/3"`).
    pub fn real_value(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(term_get_real_value(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return `true` if this term is a constant array value.
    pub fn is_const_array(&self) -> bool {
        unsafe { term_is_const_array(self.inner) }
    }
    /// Get the base (default) value of a constant array.
    pub fn const_array_base(&self) -> Term<'tm> {
        Term::from_raw(unsafe { term_get_const_array_base(self.inner) })
    }

    /// Return `true` if this term is a bit-vector value.
    pub fn is_bv_value(&self) -> bool {
        unsafe { term_is_bv_value(self.inner) }
    }
    /// Get the bit-vector value as a string in the given base (2, 10, or 16).
    pub fn bv_value(&self, base: u32) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(term_get_bv_value(self.inner, base))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return `true` if this term is a finite field value.
    pub fn is_ff_value(&self) -> bool {
        unsafe { term_is_ff_value(self.inner) }
    }
    /// Get the finite field value as a string.
    pub fn ff_value(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(term_get_ff_value(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return `true` if this term is an uninterpreted sort value.
    pub fn is_uninterpreted_sort_value(&self) -> bool {
        unsafe { term_is_uninterpreted_sort_value(self.inner) }
    }
    /// Get the uninterpreted sort value as a string.
    pub fn uninterpreted_sort_value(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(term_get_uninterpreted_sort_value(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Return `true` if this term is a tuple value.
    pub fn is_tuple_value(&self) -> bool {
        unsafe { term_is_tuple_value(self.inner) }
    }
    /// Get the elements of a tuple value.
    pub fn tuple_value(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { term_get_tuple_value(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Return `true` if this term is a rounding mode value.
    pub fn is_rm_value(&self) -> bool {
        unsafe { term_is_rm_value(self.inner) }
    }
    /// Get the rounding mode value.
    pub fn rm_value(&self) -> cvc5_ff_sys::RoundingMode {
        unsafe { term_get_rm_value(self.inner) }
    }

    /// Return `true` if this term is positive zero (`+0.0`).
    pub fn is_fp_pos_zero(&self) -> bool {
        unsafe { term_is_fp_pos_zero(self.inner) }
    }
    /// Return `true` if this term is negative zero (`-0.0`).
    pub fn is_fp_neg_zero(&self) -> bool {
        unsafe { term_is_fp_neg_zero(self.inner) }
    }
    /// Return `true` if this term is positive infinity.
    pub fn is_fp_pos_inf(&self) -> bool {
        unsafe { term_is_fp_pos_inf(self.inner) }
    }
    /// Return `true` if this term is negative infinity.
    pub fn is_fp_neg_inf(&self) -> bool {
        unsafe { term_is_fp_neg_inf(self.inner) }
    }
    /// Return `true` if this term is NaN.
    pub fn is_fp_nan(&self) -> bool {
        unsafe { term_is_fp_nan(self.inner) }
    }
    /// Return `true` if this term is a floating-point value.
    pub fn is_fp_value(&self) -> bool {
        unsafe { term_is_fp_value(self.inner) }
    }
    /// Get the floating-point value as `(exponent_width, significand_width, bit_vector_value)`.
    pub fn fp_value(&self) -> (u32, u32, Term<'tm>) {
        let (mut ew, mut sw) = (0u32, 0u32);
        let mut val = std::ptr::null_mut();
        unsafe { term_get_fp_value(self.inner, &mut ew, &mut sw, &mut val) };
        (ew, sw, Term::from_raw(val))
    }

    /// Return `true` if this term is a set value.
    pub fn is_set_value(&self) -> bool {
        unsafe { term_is_set_value(self.inner) }
    }
    /// Get the elements of a set value.
    pub fn set_value(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { term_get_set_value(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Return `true` if this term is a sequence value.
    pub fn is_sequence_value(&self) -> bool {
        unsafe { term_is_sequence_value(self.inner) }
    }
    /// Get the elements of a sequence value.
    pub fn sequence_value(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { term_get_sequence_value(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Return `true` if this term is a cardinality constraint.
    pub fn is_cardinality_constraint(&self) -> bool {
        unsafe { term_is_cardinality_constraint(self.inner) }
    }
    /// Get the sort and upper bound of a cardinality constraint.
    pub fn cardinality_constraint(&self) -> (Sort<'tm>, u32) {
        let mut sort = std::ptr::null_mut();
        let mut upper = 0u32;
        unsafe { term_get_cardinality_constraint(self.inner, &mut sort, &mut upper) };
        (Sort::from_raw(sort), upper)
    }

    /// Return `true` if this term is a real algebraic number.
    pub fn is_real_algebraic_number(&self) -> bool {
        unsafe { term_is_real_algebraic_number(self.inner) }
    }
    /// Get the defining polynomial of a real algebraic number in terms of variable `v`.
    pub fn real_algebraic_number_defining_polynomial(&self, v: Term) -> Term<'tm> {
        Term::from_raw(unsafe {
            term_get_real_algebraic_number_defining_polynomial(self.inner, v.inner)
        })
    }
    /// Get the lower bound of the isolating interval of a real algebraic number.
    pub fn real_algebraic_number_lower_bound(&self) -> Term<'tm> {
        Term::from_raw(unsafe { term_get_real_algebraic_number_lower_bound(self.inner) })
    }
    /// Get the upper bound of the isolating interval of a real algebraic number.
    pub fn real_algebraic_number_upper_bound(&self) -> Term<'tm> {
        Term::from_raw(unsafe { term_get_real_algebraic_number_upper_bound(self.inner) })
    }

    /// Return `true` if this term is a Skolem.
    pub fn is_skolem(&self) -> bool {
        unsafe { term_is_skolem(self.inner) }
    }
    /// Get the Skolem identifier of this term.
    pub fn skolem_id(&self) -> cvc5_ff_sys::SkolemId {
        unsafe { term_get_skolem_id(self.inner) }
    }
    /// Get the indices of this Skolem term.
    pub fn skolem_indices(&self) -> Vec<Term<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { term_get_skolem_indices(self.inner, &mut size) };
        (0..size)
            .map(|i| Term::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }
}

impl fmt::Display for Term<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { term_to_string(self.inner) };
        let cs = unsafe { std::ffi::CStr::from_ptr(s) };
        write!(f, "{}", cs.to_string_lossy())
    }
}

impl fmt::Debug for Term<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Term({self})")
    }
}

impl PartialEq for Term<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { term_is_equal(self.inner, other.inner) }
    }
}

impl Eq for Term<'_> {}

impl PartialOrd for Term<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let c = unsafe { term_compare(self.inner, other.inner) };
        c.cmp(&0)
    }
}

impl std::hash::Hash for Term<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { term_hash(self.inner) }.hash(state);
    }
}
