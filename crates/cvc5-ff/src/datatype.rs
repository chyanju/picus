use cvc5_ff_sys::*;
use std::ffi::CString;
use std::fmt;
use std::marker::PhantomData;

use crate::{Sort, Term};

// ---------------------------------------------------------------------------
// DatatypeConstructorDecl
// ---------------------------------------------------------------------------

/// A declaration for a datatype constructor (before the datatype is resolved).
pub struct DatatypeConstructorDecl<'tm> {
    pub(crate) inner: cvc5_ff_sys::DatatypeConstructorDecl,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for DatatypeConstructorDecl<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { dt_cons_decl_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for DatatypeConstructorDecl<'_> {
    fn drop(&mut self) {
        unsafe { dt_cons_decl_release(self.inner) }
    }
}

impl<'tm> DatatypeConstructorDecl<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::DatatypeConstructorDecl) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Add a selector with the given name and codomain sort.
    pub fn add_selector(&mut self, name: &str, sort: Sort) {
        let c = CString::new(name).unwrap();
        unsafe { dt_cons_decl_add_selector(self.inner, c.as_ptr(), sort.inner) }
    }

    /// Add a selector whose codomain is the datatype itself (self-reference).
    pub fn add_selector_self(&mut self, name: &str) {
        let c = CString::new(name).unwrap();
        unsafe { dt_cons_decl_add_selector_self(self.inner, c.as_ptr()) }
    }

    /// Add a selector whose codomain is an unresolved datatype with the given name.
    pub fn add_selector_unresolved(&mut self, name: &str, unres_name: &str) {
        let n = CString::new(name).unwrap();
        let u = CString::new(unres_name).unwrap();
        unsafe { dt_cons_decl_add_selector_unresolved(self.inner, n.as_ptr(), u.as_ptr()) }
    }
}

impl fmt::Display for DatatypeConstructorDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { dt_cons_decl_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

impl PartialEq for DatatypeConstructorDecl<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { dt_cons_decl_is_equal(self.inner, other.inner) }
    }
}
impl Eq for DatatypeConstructorDecl<'_> {}

impl std::hash::Hash for DatatypeConstructorDecl<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { dt_cons_decl_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for DatatypeConstructorDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatatypeConstructorDecl({self})")
    }
}

// ---------------------------------------------------------------------------
// DatatypeDecl
// ---------------------------------------------------------------------------

/// A declaration for a datatype (before it is resolved into a sort).
pub struct DatatypeDecl<'tm> {
    pub(crate) inner: cvc5_ff_sys::DatatypeDecl,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for DatatypeDecl<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { dt_decl_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for DatatypeDecl<'_> {
    fn drop(&mut self) {
        unsafe { dt_decl_release(self.inner) }
    }
}

impl<'tm> DatatypeDecl<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::DatatypeDecl) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Create a copy of this declaration (increments the internal reference count).
    pub fn copy(&self) -> DatatypeDecl<'tm> {
        DatatypeDecl::from_raw(unsafe { dt_decl_copy(self.inner) })
    }

    /// Add a constructor declaration to this datatype.
    pub fn add_constructor(&mut self, ctor: &DatatypeConstructorDecl) {
        unsafe { dt_decl_add_constructor(self.inner, ctor.inner) }
    }

    /// Get the number of constructors in this declaration.
    pub fn num_constructors(&self) -> usize {
        unsafe { dt_decl_get_num_constructors(self.inner) }
    }

    /// Return `true` if this datatype declaration is parametric.
    pub fn is_parametric(&self) -> bool {
        unsafe { dt_decl_is_parametric(self.inner) }
    }

    /// Return `true` if this datatype declaration has been resolved.
    pub fn is_resolved(&self) -> bool {
        unsafe { dt_decl_is_resolved(self.inner) }
    }

    /// Get the name of this datatype declaration.
    pub fn name(&self) -> &str {
        unsafe {
            std::ffi::CStr::from_ptr(dt_decl_get_name(self.inner))
                .to_str()
                .unwrap_or("")
        }
    }
}

impl fmt::Display for DatatypeDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { dt_decl_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

impl PartialEq for DatatypeDecl<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { dt_decl_is_equal(self.inner, other.inner) }
    }
}
impl Eq for DatatypeDecl<'_> {}

impl std::hash::Hash for DatatypeDecl<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { dt_decl_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for DatatypeDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatatypeDecl({self})")
    }
}

// ---------------------------------------------------------------------------
// DatatypeSelector
// ---------------------------------------------------------------------------

/// A selector of a resolved datatype constructor.
pub struct DatatypeSelector<'tm> {
    pub(crate) inner: cvc5_ff_sys::DatatypeSelector,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for DatatypeSelector<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { dt_sel_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for DatatypeSelector<'_> {
    fn drop(&mut self) {
        unsafe { dt_sel_release(self.inner) }
    }
}

impl<'tm> DatatypeSelector<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::DatatypeSelector) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Create a copy of this selector (increments the internal reference count).
    pub fn copy(&self) -> DatatypeSelector<'tm> {
        DatatypeSelector::from_raw(unsafe { dt_sel_copy(self.inner) })
    }

    /// Get the name of this selector.
    pub fn name(&self) -> &str {
        unsafe {
            std::ffi::CStr::from_ptr(dt_sel_get_name(self.inner))
                .to_str()
                .unwrap_or("")
        }
    }

    /// Get the selector function as a term.
    pub fn term(&self) -> Term<'tm> {
        Term::from_raw(unsafe { dt_sel_get_term(self.inner) })
    }

    /// Get the updater function as a term.
    pub fn updater_term(&self) -> Term<'tm> {
        Term::from_raw(unsafe { dt_sel_get_updater_term(self.inner) })
    }

    /// Get the codomain (return) sort of this selector.
    pub fn codomain_sort(&self) -> Sort<'tm> {
        Sort::from_raw(unsafe { dt_sel_get_codomain_sort(self.inner) })
    }
}

impl fmt::Display for DatatypeSelector<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { dt_sel_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

impl PartialEq for DatatypeSelector<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { dt_sel_is_equal(self.inner, other.inner) }
    }
}
impl Eq for DatatypeSelector<'_> {}

impl std::hash::Hash for DatatypeSelector<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { dt_sel_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for DatatypeSelector<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatatypeSelector({self})")
    }
}

// ---------------------------------------------------------------------------
// DatatypeConstructor
// ---------------------------------------------------------------------------

/// A constructor of a resolved datatype.
pub struct DatatypeConstructor<'tm> {
    pub(crate) inner: cvc5_ff_sys::DatatypeConstructor,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for DatatypeConstructor<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { dt_cons_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for DatatypeConstructor<'_> {
    fn drop(&mut self) {
        unsafe { dt_cons_release(self.inner) }
    }
}

impl<'tm> DatatypeConstructor<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::DatatypeConstructor) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Get the name of this constructor.
    pub fn name(&self) -> &str {
        unsafe {
            std::ffi::CStr::from_ptr(dt_cons_get_name(self.inner))
                .to_str()
                .unwrap_or("")
        }
    }

    /// Get the constructor function as a term.
    pub fn term(&self) -> Term<'tm> {
        Term::from_raw(unsafe { dt_cons_get_term(self.inner) })
    }

    /// Get the constructor term instantiated for the given parametric datatype sort.
    pub fn instantiated_term(&self, sort: Sort) -> Term<'tm> {
        Term::from_raw(unsafe { dt_cons_get_instantiated_term(self.inner, sort.inner) })
    }

    /// Get the tester (discriminator) function as a term.
    pub fn tester_term(&self) -> Term<'tm> {
        Term::from_raw(unsafe { dt_cons_get_tester_term(self.inner) })
    }

    /// Get the number of selectors of this constructor.
    pub fn num_selectors(&self) -> usize {
        unsafe { dt_cons_get_num_selectors(self.inner) }
    }

    /// Get the selector at the given index.
    pub fn selector(&self, index: usize) -> DatatypeSelector<'tm> {
        DatatypeSelector::from_raw(unsafe { dt_cons_get_selector(self.inner, index) })
    }

    /// Get a selector by name.
    pub fn selector_by_name(&self, name: &str) -> DatatypeSelector<'tm> {
        let c = CString::new(name).unwrap();
        DatatypeSelector::from_raw(unsafe { dt_cons_get_selector_by_name(self.inner, c.as_ptr()) })
    }
}

impl fmt::Display for DatatypeConstructor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { dt_cons_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

impl PartialEq for DatatypeConstructor<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { dt_cons_is_equal(self.inner, other.inner) }
    }
}
impl Eq for DatatypeConstructor<'_> {}

impl std::hash::Hash for DatatypeConstructor<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { dt_cons_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for DatatypeConstructor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DatatypeConstructor({self})")
    }
}

// ---------------------------------------------------------------------------
// Datatype
// ---------------------------------------------------------------------------

/// A resolved datatype.
///
/// Obtained from a sort via [`Sort::datatype`] after the datatype has been
/// created with [`TermManager::mk_dt_sort`](crate::TermManager::mk_dt_sort).
pub struct Datatype<'tm> {
    pub(crate) inner: cvc5_ff_sys::Datatype,
    pub(crate) _phantom: PhantomData<&'tm ()>,
}

impl Clone for Datatype<'_> {
    fn clone(&self) -> Self {
        Self {
            inner: unsafe { dt_copy(self.inner) },
            _phantom: PhantomData,
        }
    }
}

impl Drop for Datatype<'_> {
    fn drop(&mut self) {
        unsafe { dt_release(self.inner) }
    }
}

impl<'tm> Datatype<'tm> {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Datatype) -> Self {
        Self {
            inner: raw,
            _phantom: PhantomData,
        }
    }

    /// Create a copy of this datatype (increments the internal reference count).
    pub fn copy(&self) -> Datatype<'tm> {
        Datatype::from_raw(unsafe { dt_copy(self.inner) })
    }

    /// Get the constructor at the given index.
    pub fn constructor(&self, index: usize) -> DatatypeConstructor<'tm> {
        DatatypeConstructor::from_raw(unsafe { dt_get_constructor(self.inner, index) })
    }

    /// Get a constructor by name.
    pub fn constructor_by_name(&self, name: &str) -> DatatypeConstructor<'tm> {
        let c = CString::new(name).unwrap();
        DatatypeConstructor::from_raw(unsafe { dt_get_constructor_by_name(self.inner, c.as_ptr()) })
    }

    /// Get a selector by name (searches all constructors).
    pub fn selector(&self, name: &str) -> DatatypeSelector<'tm> {
        let c = CString::new(name).unwrap();
        DatatypeSelector::from_raw(unsafe { dt_get_selector(self.inner, c.as_ptr()) })
    }

    /// Get the name of this datatype.
    pub fn name(&self) -> &str {
        unsafe {
            std::ffi::CStr::from_ptr(dt_get_name(self.inner))
                .to_str()
                .unwrap_or("")
        }
    }

    /// Get the number of constructors.
    pub fn num_constructors(&self) -> usize {
        unsafe { dt_get_num_constructors(self.inner) }
    }

    /// Get the sort parameters of a parametric datatype.
    pub fn parameters(&self) -> Vec<Sort<'tm>> {
        let mut size = 0usize;
        let ptr = unsafe { dt_get_parameters(self.inner, &mut size) };
        (0..size)
            .map(|i| Sort::from_raw(unsafe { *ptr.add(i) }))
            .collect()
    }

    /// Return `true` if this datatype is parametric.
    pub fn is_parametric(&self) -> bool {
        unsafe { dt_is_parametric(self.inner) }
    }

    /// Return `true` if this is a codatatype.
    pub fn is_codatatype(&self) -> bool {
        unsafe { dt_is_codatatype(self.inner) }
    }

    /// Return `true` if this is a tuple datatype.
    pub fn is_tuple(&self) -> bool {
        unsafe { dt_is_tuple(self.inner) }
    }

    /// Return `true` if this is a record datatype.
    pub fn is_record(&self) -> bool {
        unsafe { dt_is_record(self.inner) }
    }

    /// Return `true` if this datatype is finite.
    pub fn is_finite(&self) -> bool {
        unsafe { dt_is_finite(self.inner) }
    }

    /// Return `true` if this datatype is well-founded.
    pub fn is_well_founded(&self) -> bool {
        unsafe { dt_is_well_founded(self.inner) }
    }
}

impl fmt::Display for Datatype<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { dt_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

impl PartialEq for Datatype<'_> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { dt_is_equal(self.inner, other.inner) }
    }
}
impl Eq for Datatype<'_> {}

impl std::hash::Hash for Datatype<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { dt_hash(self.inner) }.hash(state);
    }
}

impl fmt::Debug for Datatype<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Datatype({self})")
    }
}
