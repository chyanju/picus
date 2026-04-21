#!/usr/bin/env bash
# benchmark_cvc5.sh — time cvc5 on the same smt2 inputs used by Criterion.
#
# Usage:  ./benchmark_cvc5.sh [N_ITERS]
#
# Produces CSV-style output: file, expected, actual, avg_ms, min_ms, max_ms

set -euo pipefail

N="${1:-100}"
CVC5="/home/ubuntu/Downloads/cvc5-repo/build/bin/cvc5"
export LD_LIBRARY_PATH="/home/ubuntu/Downloads/cvc5-repo/build/lib:${LD_LIBRARY_PATH:-}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SMT2_DIR="$SCRIPT_DIR/smt2"

if [ ! -x "$CVC5" ]; then
    echo "ERROR: cvc5 not found at $CVC5" >&2
    exit 1
fi

echo "benchmark,expected,actual,iters,avg_us,min_us,max_us"

for smt2_file in "$SMT2_DIR"/*.smt2; do
    name="$(basename "$smt2_file" .smt2)"

    # Determine expected result from file header
    expected=$(grep -oP 'EXPECT:\s*\K\S+' "$smt2_file" 2>/dev/null || echo "unknown")

    total_us=0
    min_us=999999999
    max_us=0
    actual=""

    for ((i=0; i<N; i++)); do
        # Time in microseconds using date +%s%N
        start=$(date +%s%N)
        result=$("$CVC5" --lang smt2 --ff-solver split "$smt2_file" 2>/dev/null || echo "error")
        end=$(date +%s%N)

        elapsed_ns=$((end - start))
        elapsed_us=$((elapsed_ns / 1000))

        total_us=$((total_us + elapsed_us))
        if [ "$elapsed_us" -lt "$min_us" ]; then min_us=$elapsed_us; fi
        if [ "$elapsed_us" -gt "$max_us" ]; then max_us=$elapsed_us; fi

        if [ "$i" -eq 0 ]; then
            # Capture the first line of output as the actual result
            actual=$(echo "$result" | head -1 | tr -d '[:space:]')
        fi
    done

    avg_us=$((total_us / N))
    echo "$name,$expected,$actual,$N,$avg_us,$min_us,$max_us"
done
