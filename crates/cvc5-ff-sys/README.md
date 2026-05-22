# cvc5-ff-sys

Raw `bindgen` bindings for cvc5 (with finite-field support). The Rust-side
wrapper lives in `../cvc5-ff/`.

## Binding regeneration

`prebuilt/bindings.rs` and `prebuilt/parser_bindings.rs` are committed
to the repo so `cargo doc` (and docs.rs builds) work without the cvc5
headers. Normal builds run `bindgen` afresh against the linked cvc5
source tree.

When cvc5 source is updated (e.g. a submodule bump or pointer change),
regenerate the prebuilt artifacts:

```bash
rm crates/cvc5-ff-sys/prebuilt/bindings.rs \
   crates/cvc5-ff-sys/prebuilt/parser_bindings.rs
cargo build -p cvc5-ff-sys
git add crates/cvc5-ff-sys/prebuilt/
```

Two environment knobs influence the build:

- `DOCS_RS=1` — skip the bindgen+compile step and copy prebuilt
  bindings verbatim. Used by docs.rs.
- `CVC5_LIB_DIR=/path/to/cvc5/lib` — link against an existing cvc5
  build instead of compiling from source. `CVC5_INCLUDE_DIR` overrides
  the header search path (defaults to `$CVC5_LIB_DIR/../include`).
