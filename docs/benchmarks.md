# Benchmarks

The `benchmarks/` directory contains Circom circuit sources from 23 real-world projects, pinned to specific git commits. These are the same benchmarks used in the PLDI 2023 paper evaluation.

## Projects

| Directory | Project | Circuits |
|-----------|---------|----------|
| `circomlib-cff5ab6` | [circomlib](https://github.com/iden3/circomlib) | 73 (gates, comparators, MiMC, EdDSA, Pedersen, ...) |
| `circomlibex-cff5ab6` | circomlib parameterized | Bit-width variants (1, 8, 16, 32, 64, 128, 253, 254, 256) |
| `semaphore-0f0fc95` | [Semaphore](https://github.com/semaphore-protocol/semaphore) | Identity proofs |
| `darkforest-eth-9033eaf-fixed` | [Dark Forest](https://github.com/darkforest-eth/darkforest-v0.6) | Game circuits |
| `hermez-network-9a696e3-fixed` | [Hermez](https://github.com/hermeznetwork/circuits) | Rollup circuits |
| `maci-9b1b1a6-fixed` | [MACI](https://github.com/privacy-scaling-explorations/maci) | Voting |
| `circom-ecdsa-d87eb70` | [circom-ecdsa](https://github.com/0xPARC/circom-ecdsa) | ECDSA verification |
| `circom-bigint-7505e5c` | [circom-bigint](https://github.com/0xPARC/circom-bigint) | Big integer arithmetic |
| `circom-pairing-743d761` | [circom-pairing](https://github.com/yi-sun/circom-pairing) | Pairing operations |
| `ed25519-099d19c-fixed` | ed25519 circuits | EdDSA over Curve25519 |
| `keccak256-circom-af3e898` | Keccak-256 | Hash function |
| `aes-circom-0784f74` | AES | Symmetric encryption |
| `circomlib-ml-adb9edd` | [circomlib-ml](https://github.com/socathie/circomlib-ml) | Machine learning |
| `circomlib-matrix-d41bae3` | Matrix operations | Linear algebra |
| `hydra-2010a65` | Hydra | Proving scheme |
| `iden3-core-56a08f9` | iden3 core | Identity |
| `motivating` | Toy examples | adder, ValidateDecoding (buggy + fixed) |
| `buggy-mix` | Known bugs | Circuits with known under-constrained signals |

## Compiling Circuits

Circuits require [circom](https://docs.circom.io/) 2.0+ to compile. The `libs/` directory contains shared dependencies.

```bash
circom benchmarks/circomlib-cff5ab6/AND@gates.circom \
  --r1cs --sym --O0 \
  --output /tmp/ \
  -l benchmarks/libs/

picus check --r1cs /tmp/AND@gates.r1cs --solver z3
```

> Use `--O0` (no optimization) to preserve the original constraint structure.

## Expected Results (circomlib-cff5ab6, weak uniqueness)

Circuits that Picus identifies as **unsafe** (under-constrained outputs):

| Circuit | Status |
|---------|--------|
| Bits2Point | unsafe |
| Point2Bits | unsafe |
| Edwards2Montgomery | unsafe |
| Montgomery2Edwards | unsafe |
| MontgomeryAdd | unsafe |
| Decoder | unsafe |

All other circomlib circuits with definitive results are **safe**. Some large circuits (Pedersen, EscalarMul, Sign, CompConstant) may time out with default settings — increase `--timeout` or use cvc5 for better finite-field performance.
