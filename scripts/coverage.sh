#!/usr/bin/env bash
# Coverage measurement for the picus-solver crate.
#
# Excludes:
#   - src/bin/* — dev/bench binaries (cvc5_compare, run_smt2) that shell
#     out to external processes; not meaningfully unit-testable.
#   - cdclt/theory.rs — Theory trait declaration + types; no executable
#     code beyond struct/enum/trait definitions.
#   - frontend/bench_fixtures.rs — bench data builders; only exercised by
#     benchmark targets, not by unit/integration tests.
#
# Run from anywhere in the workspace; the script chdirs to the repo root.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

EXCLUDE='src/bin/|cdclt/theory\.rs|frontend/bench_fixtures\.rs'

case "${1:-summary}" in
    summary)
        exec cargo llvm-cov -p picus-solver --summary-only \
            --ignore-filename-regex "$EXCLUDE"
        ;;
    full)
        exec cargo llvm-cov -p picus-solver \
            --ignore-filename-regex "$EXCLUDE"
        ;;
    html)
        exec cargo llvm-cov -p picus-solver --html \
            --ignore-filename-regex "$EXCLUDE"
        ;;
    *)
        echo "usage: $0 [summary|full|html]" >&2
        exit 2
        ;;
esac
