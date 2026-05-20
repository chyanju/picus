#!/usr/bin/env bash
# regression.sh — fast regression suite for picus-solver / picus-cli.
#
# Two tiers:
#   Tier 1 — algorithmic correctness via `cargo test -p picus-solver --release`
#            (132 unit + integration tests, ~4 s).
#   Tier 2 — R1CS-level smoke against a curated circomlib subset, run through
#            the native finite-field backend and compared to expected verdicts
#            (~30-60 s once the binary and circuits are built).
#
# Usage:
#   scripts/regression.sh                # both tiers
#   scripts/regression.sh --tier1-only   # cargo test only (fast)
#   scripts/regression.sh --tier2-only   # R1CS smoke only (assumes Tier 1 already ran)
#
# Exit status: 0 = all pass, 1 = any failure.

set -euo pipefail

cd "$(dirname "$0")/.."

PICUS_BIN="target/release/picus"
CIRCUIT_DIR="benchmarks/circom/circomlib-cff5ab6"
TIMEOUT_MS=5000

# Per-fixture expected verdict. Choose small/fast circuits that exercise both
# safe and unsafe paths through the native solver. Avoids known slow circuits
# (BitElementMulAny, Pedersen, anything from ed25519/keccak/pairing).
#
# Unsafe expectations match docs/benchmarks.md § Expected Results.
FIXTURES=(
    # safe expected
    "AND@gates safe"
    "OR@gates safe"
    "NAND@gates safe"
    "IsZero@comparators safe"
    "IsEqual@comparators safe"
    "Mux1@mux1 safe"
    "Switcher@switcher safe"
    "Sigma@poseidon safe"
    "MultiAND@gates safe"
    "MultiMux1@mux1 safe"
    # unsafe expected
    "Decoder@multiplexer unsafe"
    "Edwards2Montgomery@montgomery unsafe"
    "Montgomery2Edwards@montgomery unsafe"
    "MontgomeryAdd@montgomery unsafe"
    "MontgomeryDouble@montgomery unsafe"
    "Bits2Point@pointbits unsafe"
    "Point2Bits@pointbits unsafe"
)

RED=$'\033[0;31m'
GREEN=$'\033[0;32m'
YELLOW=$'\033[0;33m'
DIM=$'\033[0;2m'
RESET=$'\033[0m'

# ─── arg parsing ─────────────────────────────────────────────────────────────
RUN_TIER1=1
RUN_TIER2=1
case "${1:-}" in
    --tier1-only) RUN_TIER2=0 ;;
    --tier2-only) RUN_TIER1=0 ;;
    --help|-h)
        sed -n '2,18p' "$0"
        exit 0 ;;
    "") ;;
    *) echo "unknown flag: $1 (try --help)" >&2; exit 2 ;;
esac

# ─── Tier 1 ──────────────────────────────────────────────────────────────────
if [ "$RUN_TIER1" = 1 ]; then
    echo "─── Tier 1: algorithmic correctness ───"
    T0=$(date +%s)
    if cargo test -p picus-solver --release 2>&1 | tee /tmp/picus-regression-tier1.log | tail -3 | grep -q "0 failed"; then
        T1=$(date +%s)
        n_passed=$(grep -oE '[0-9]+ passed' /tmp/picus-regression-tier1.log | awk '{s+=$1} END{print s}')
        echo "${GREEN}✓${RESET} ${n_passed} tests passed ($((T1-T0))s)"
    else
        echo "${RED}✗${RESET} algorithmic tests failed"
        tail -50 /tmp/picus-regression-tier1.log
        exit 1
    fi
    echo ""
fi

# ─── Tier 2 ──────────────────────────────────────────────────────────────────
if [ "$RUN_TIER2" = 1 ]; then
    echo "─── Tier 2: R1CS smoke (${#FIXTURES[@]} circomlib circuits) ───"

    if [ ! -x "$PICUS_BIN" ]; then
        echo "${YELLOW}picus-cli not built; running cargo build --release -p picus-cli${RESET}"
        echo "${DIM}(first build compiles cvc5 + z3, ~12 min)${RESET}"
        cargo build --release -p picus-cli
    fi

    if [ ! -d "$CIRCUIT_DIR" ]; then
        echo "${YELLOW}benchmarks submodule not initialised; running git submodule update --init${RESET}"
        git submodule update --init benchmarks
    fi

    # Compile any missing circuits.
    missing=()
    for entry in "${FIXTURES[@]}"; do
        name="${entry% *}"
        [ -f "$CIRCUIT_DIR/$name.r1cs" ] || missing+=("$name")
    done
    if [ "${#missing[@]}" -gt 0 ]; then
        if ! command -v circom >/dev/null; then
            echo "${RED}✗${RESET} circom not on PATH; cannot compile ${#missing[@]} missing circuit(s)"
            exit 1
        fi
        echo "${DIM}Compiling ${#missing[@]} missing circuit(s)...${RESET}"
        ( cd benchmarks/circom && for n in "${missing[@]}"; do
            ./compile.sh build-file "circomlib-cff5ab6/$n.circom" >/dev/null 2>&1
        done )
    fi

    pass=0
    fail=0
    failed_names=()
    T0=$(date +%s)

    for entry in "${FIXTURES[@]}"; do
        name="${entry% *}"
        expected="${entry##* }"
        r1cs="$CIRCUIT_DIR/$name.r1cs"

        json=$("$PICUS_BIN" check \
            --r1cs "$r1cs" \
            --solver native --theory ff \
            --timeout "$TIMEOUT_MS" \
            --format json 2>/dev/null || true)

        # Top-level "result" field is one of: safe / unsafe / unknown.
        actual=$(printf '%s' "$json" \
            | grep -E '^[[:space:]]*"result"' \
            | head -1 \
            | sed -E 's/.*"result"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/')

        if [ "$actual" = "$expected" ]; then
            printf '  %s✓%s %-44s → %s\n' "$GREEN" "$RESET" "$name" "$actual"
            pass=$((pass+1))
        else
            printf '  %s✗%s %-44s → expected %s, got %s\n' \
                "$RED" "$RESET" "$name" "$expected" "${actual:-<no output>}"
            fail=$((fail+1))
            failed_names+=("$name")
        fi
    done

    T1=$(date +%s)
    echo ""
    echo "─── Tier 2 summary ───"
    echo "Passed: $pass / ${#FIXTURES[@]}    Time: $((T1-T0))s"
    if [ "$fail" -gt 0 ]; then
        printf '%sFAILED:%s\n' "$RED" "$RESET"
        for n in "${failed_names[@]}"; do echo "  - $n"; done
        exit 1
    fi
fi

echo ""
echo "${GREEN}✓ regression passed${RESET}"
