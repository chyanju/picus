//! CDCL(T) vs DNF wall-time comparison on the
//! `bench_fixtures::corpus` workloads. Workload families and sizes
//! are defined in `picus_solver::bench_fixtures`.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use picus_solver::bench_fixtures::corpus;
use picus_solver::boolean::{solve_boolean_query_dnf, BooleanQuery};
use picus_solver::cdclt::solve_formula;
use picus_solver::smt2::parse_boolean;
use picus_core::timeout::CancelToken;

fn bench_paths(c: &mut Criterion, family: &str, label: String, q: BooleanQuery) {
    let mut group = c.benchmark_group(format!("cdclt_vs_dnf/{}", family));
    let cancel = CancelToken::none();
    let prime = q.prime.clone();
    let formula = q.formula.clone();
    let var_names: Vec<String> = q.var_names().to_vec();
    group.bench_with_input(BenchmarkId::new("cdclt", &label), &(), |b, _| {
        b.iter(|| {
            let r = solve_formula(prime.clone(), &var_names, black_box(&formula), &cancel);
            black_box(r);
        });
    });
    group.bench_with_input(BenchmarkId::new("dnf", &label), &(), |b, _| {
        b.iter(|| {
            let r = solve_boolean_query_dnf(black_box(&q), &cancel);
            black_box(r);
        });
    });
    group.finish();
}

fn bench_cdclt(c: &mut Criterion) {
    for (family, label, src) in corpus() {
        let q = parse_boolean(&src).expect("parse");
        bench_paths(c, family, label, q);
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(15);
    targets = bench_cdclt
}
criterion_main!(benches);
