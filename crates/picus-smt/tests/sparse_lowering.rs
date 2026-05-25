//! Resident-memory footprint of lowering a wide circuit to `PolyIR`.
//!
//! EdDSAPoseidon has ~21k wires, so its two-copy uniqueness ring has
//! ~42k variables. With the dense representation each monomial is a
//! full-length exponent vector (O(n_vars)), so `PolyIR::equalities`
//! alone needs tens of GB and lowering OOMs before any solving begins.
//! The sparse representation stores only the nonzero `(var, exp)` pairs
//! (O(nnz) per term), so the same IR fits in megabytes.
//!
//! Ignored by default (loads a ~3 MB benchmark and builds a 42k-variable
//! IR). Run it with the sparse representation:
//!
//! ```text
//! PICUS_POLY_REPR=sparse \
//!   cargo test -p picus-smt --test sparse_lowering -- --ignored --nocapture
//! ```
//!
//! Do NOT run it under the dense representation on this circuit; that is
//! the resident-memory blow-up the sparse representation avoids.

use std::collections::HashSet;

#[test]
#[ignore = "loads a large benchmark; run with PICUS_POLY_REPR=sparse -- --ignored --nocapture"]
fn eddsa_poseidon_lowering_footprint() {
    let path = std::path::Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/circom/circomlib-cff5ab6/EdDSAPoseidonVerifier@eddsaposeidon.r1cs"
    ));
    let Ok(r1cs) = picus_r1cs::parser::read_r1cs_file(path) else {
        eprintln!("skipping: fixture not found at {}", path.display());
        return;
    };

    let repr = picus_core::config::with(|c| c.poly_repr);

    // Lowering only — no backend, no Gröbner solve.
    let known = HashSet::new();
    let ir = picus_smt::poly_ir::r1cs_to_poly_ir(&r1cs, &known, 0)
        .expect("lowering should succeed");

    let n_vars = ir.ring.n_vars();
    let n_eq = ir.equalities.len();
    let mut total_terms = 0usize;
    let mut total_nnz = 0usize;
    for poly in &ir.equalities {
        for (_coeff, vars) in ir.poly_terms_idx(poly) {
            total_terms += 1;
            total_nnz += vars.len();
        }
    }

    // Sparse keeps ~6 bytes per nonzero entry (4-byte var + 2-byte exp);
    // dense would keep an n_vars-long u16 exponent vector per term.
    let sparse_mono_bytes = total_nnz * 6;
    let dense_mono_bytes = total_terms.saturating_mul(n_vars).saturating_mul(2);

    eprintln!(
        "EdDSAPoseidon lowering [{:?}]: n_vars={}, equalities={}, terms={}, nnz={}",
        repr, n_vars, n_eq, total_terms, total_nnz
    );
    eprintln!(
        "  monomial storage: sparse ≈ {} KiB vs dense ≈ {} MiB ({}x smaller)",
        sparse_mono_bytes / 1024,
        dense_mono_bytes / (1024 * 1024),
        if sparse_mono_bytes > 0 { dense_mono_bytes / sparse_mono_bytes } else { 0 }
    );

    // The DPVL setup also runs `wire_connectivity_score`, which reads
    // every equality via `appearing_indeterminates` before any solve.
    // Confirm that read path is cheap under sparse (no densification): it
    // localises memory cost away from the IR representation.
    {
        use std::collections::{HashMap, HashSet};
        let mut counter: HashMap<usize, usize> = HashMap::new();
        for poly in &ir.equalities {
            let mut seen: HashSet<usize> = HashSet::new();
            for v in ir.ring.appearing_indeterminates(poly).iter() {
                seen.insert(ir.var_to_wire(v));
            }
            for w in seen {
                *counter.entry(w).or_insert(0) += 1;
            }
        }
        eprintln!("  connectivity wires touched: {}", counter.len());
    }

    assert!(n_vars > 40_000, "EdDSAPoseidon should be a wide two-copy ring");
    assert!(total_terms > 0, "lowering must produce equalities");
    // The assertion that matters is implicit: under the sparse rep this
    // function returns instead of OOM-killing the process.
}
