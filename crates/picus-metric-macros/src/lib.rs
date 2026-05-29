//! Procedural macros for the `metric` profiling family.
//!
//! Provides the `#[metric]` attribute: whole-function wall-clock timing that
//! lives on the signature, so the function body stays free of profiling
//! statements. It is the item-level counterpart of the `metric::*!`
//! statement/expression macros (`incr!` / `add!` / `max!` / `timer!`) defined
//! in `picus-core`; together they let every profiling site be recognised by
//! `grep -E 'metric::|#\[metric\]'`, syntactically distinct from main logic.

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, LitStr};

/// Time the annotated function under the phase profiler (the `--profile`
/// table), via a [`ScopedTimer`] guard inserted at the top of the body.
///
/// * `#[metric]` — label is the function name.
/// * `#[metric("custom_label")]` — explicit label.
///
/// The guard is cheap when profiling is disabled (a single flag read);
/// equivalent to a hand-written `let _t = ScopedTimer::new("fn");` as the
/// first statement.
///
/// The expansion references `::picus_core::profile::ScopedTimer`, so the
/// annotated item must live in a crate that depends on `picus-core`. Inside
/// `picus-core` itself, add `extern crate self as picus_core;`.
///
/// [`ScopedTimer`]: ../picus_core/profile/struct.ScopedTimer.html
#[proc_macro_attribute]
pub fn metric(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    let label = if attr.is_empty() {
        func.sig.ident.to_string()
    } else {
        let lit = parse_macro_input!(attr as LitStr);
        lit.value()
    };

    let attrs = &func.attrs;
    let vis = &func.vis;
    let sig = &func.sig;
    let stmts = &func.block.stmts;

    quote! {
        #(#attrs)*
        #vis #sig {
            let _metric_fn_guard = ::picus_core::profile::ScopedTimer::new(#label);
            #(#stmts)*
        }
    }
    .into()
}
