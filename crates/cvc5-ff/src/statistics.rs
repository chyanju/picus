use cvc5_ff_sys::*;
use std::ffi::CString;
use std::fmt;

/// Solver statistics collected during solving.
pub struct Statistics {
    pub(crate) inner: cvc5_ff_sys::Statistics,
}

impl Statistics {
    pub(crate) fn from_raw(raw: cvc5_ff_sys::Statistics) -> Self {
        Self { inner: raw }
    }

    /// Look up a statistic by name.
    pub fn get(&self, name: &str) -> Stat {
        let c = CString::new(name).unwrap();
        Stat {
            inner: unsafe { stats_get(self.inner, c.as_ptr()) },
        }
    }

    /// Initialize the statistics iterator.
    ///
    /// - `internal` — include internal (non-public) statistics.
    /// - `dflt` — include statistics that still have their default value.
    pub fn iter_init(&self, internal: bool, dflt: bool) {
        unsafe { stats_iter_init(self.inner, internal, dflt) }
    }

    /// Return `true` if the iterator has more elements.
    pub fn iter_has_next(&self) -> bool {
        unsafe { stats_iter_has_next(self.inner) }
    }

    /// Advance the iterator and return the next `(name, stat)` pair.
    pub fn iter_next(&self) -> (String, Stat) {
        let mut name: *const std::os::raw::c_char = std::ptr::null();
        let s = unsafe { stats_iter_next(self.inner, &mut name) };
        let n = unsafe {
            std::ffi::CStr::from_ptr(name)
                .to_string_lossy()
                .into_owned()
        };
        (n, Stat { inner: s })
    }

    /// Advance the iterator and return only the next [`Stat`], ignoring the name.
    pub fn iter_next_stat(&self) -> Stat {
        self.iter_next().1
    }
}

impl fmt::Debug for Statistics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Statistics({self})")
    }
}

impl fmt::Display for Statistics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { stats_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}

/// A single statistic value.
pub struct Stat {
    pub(crate) inner: cvc5_ff_sys::Stat,
}

impl Stat {
    /// Return `true` if this is an internal (non-public) statistic.
    pub fn is_internal(&self) -> bool {
        unsafe { stat_is_internal(self.inner) }
    }

    /// Return `true` if this statistic still has its default value.
    pub fn is_default(&self) -> bool {
        unsafe { stat_is_default(self.inner) }
    }

    /// Return `true` if this statistic holds an integer value.
    pub fn is_int(&self) -> bool {
        unsafe { stat_is_int(self.inner) }
    }

    /// Return `true` if this statistic holds a double value.
    pub fn is_double(&self) -> bool {
        unsafe { stat_is_double(self.inner) }
    }

    /// Return `true` if this statistic holds a string value.
    pub fn is_string(&self) -> bool {
        unsafe { stat_is_string(self.inner) }
    }

    /// Return `true` if this statistic holds a histogram.
    pub fn is_histogram(&self) -> bool {
        unsafe { stat_is_histogram(self.inner) }
    }

    /// Get the integer value of this statistic.
    pub fn get_int(&self) -> i64 {
        unsafe { stat_get_int(self.inner) }
    }

    /// Get the double value of this statistic.
    pub fn get_double(&self) -> f64 {
        unsafe { stat_get_double(self.inner) }
    }

    /// Get the string value of this statistic.
    pub fn get_string(&self) -> String {
        unsafe {
            std::ffi::CStr::from_ptr(stat_get_string(self.inner))
                .to_string_lossy()
                .into_owned()
        }
    }

    /// Get the histogram value as a list of `(key, count)` pairs.
    pub fn get_histogram(&self) -> Vec<(String, u64)> {
        let mut keys: *mut *const std::os::raw::c_char = std::ptr::null_mut();
        let mut values: *mut u64 = std::ptr::null_mut();
        let mut size = 0usize;
        unsafe { stat_get_histogram(self.inner, &mut keys, &mut values, &mut size) };
        (0..size)
            .map(|i| unsafe {
                let k = std::ffi::CStr::from_ptr(*keys.add(i))
                    .to_string_lossy()
                    .into_owned();
                let v = *values.add(i);
                (k, v)
            })
            .collect()
    }
}

impl fmt::Debug for Stat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Stat({self})")
    }
}

impl fmt::Display for Stat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = unsafe { stat_to_string(self.inner) };
        write!(f, "{}", unsafe {
            std::ffi::CStr::from_ptr(s).to_string_lossy()
        })
    }
}
