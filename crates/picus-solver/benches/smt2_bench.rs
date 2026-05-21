//! Parse + solve wall-time on the in-tree QF_FF SMT-LIB fixtures.
//!
//! Each fixture under `benches/smt2/` is embedded at compile time via
//! `include_str!` and timed through `parse → solve_formula`. The set
//! is the subset of `cvc5/test/regress/cli/regress0/ff/` that the
//! picus-solver SMT-LIB parser handles today (no Boolean-typed
//! variables, no term-level `ite`, no Boolean iff).

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use picus_solver::cdclt::solve_formula;
use picus_solver::smt2::parse_boolean;
use picus_solver::timeout::CancelToken;

const FIXTURES: &[(&str, &str)] = &[
    (
        "field_poly",
        include_str!("smt2/field_poly.smt2"),
    ),
    (
        "issue10937",
        include_str!("smt2/issue10937.smt2"),
    ),
    (
        "univar_conjunction_sat",
        include_str!("smt2/univar_conjunction_sat.smt2"),
    ),
    (
        "univar_conjunction_unsat",
        include_str!("smt2/univar_conjunction_unsat.smt2"),
    ),
];

fn bench_smt2(c: &mut Criterion) {
    let mut group = c.benchmark_group("smt2");
    let cancel = CancelToken::none();

    for (name, src) in FIXTURES {
        group.bench_with_input(BenchmarkId::new("parse_only", name), src, |b, src| {
            b.iter(|| {
                let q = parse_boolean(black_box(src)).expect("parse");
                black_box(q);
            });
        });
        let q = parse_boolean(src).expect("parse");
        let prime = q.prime.clone();
        let formula = q.formula.clone();
        group.bench_with_input(BenchmarkId::new("solve", name), &(), |b, _| {
            b.iter(|| {
                let r = solve_formula(prime.clone(), black_box(&formula), &cancel);
                black_box(r);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_smt2);
criterion_main!(benches);
