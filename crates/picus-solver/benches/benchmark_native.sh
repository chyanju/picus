#!/usr/bin/env bash
# benchmark_native.sh — time picus-solver on equivalent workloads.
#
# Uses the test binary's built-in benchmarks (via `cargo test --release`)
# and also runs the Criterion benchmarks for comparison.
#
# Usage:  ./benchmark_native.sh

set -euo pipefail

PICUS_DIR="$(cd "$(dirname "$0")/../../.." && pwd)"

echo "=== Criterion benchmarks ==="
cd "$PICUS_DIR"
rustup run nightly cargo bench -p picus-solver --bench solver_bench 2>&1 | grep -E "^(encode|end_to_end|find_roots)" -A1

echo ""
echo "=== Probe benchmark (issue10937, single run) ==="
rustup run nightly cargo test -p picus-solver --test probe --release -- --ignored --nocapture probe_issue10937 2>&1 | grep -E "µs|ms|Phase"
