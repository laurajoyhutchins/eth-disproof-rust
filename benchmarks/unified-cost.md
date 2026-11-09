# Unified exact solver cost experiment

This experiment is opt-in, not a per-commit latency gate.

```bash
python -m pip install -e '.[test]'
python -m pytest -q tests/benchmark/test_unified_cost.py
python -m benchmarks.unified_cost --cases parity-2wire sudoku-4wire nested-2wire --variants reference plans --repeats 3 --output artifacts/unified-cost.json
```

The optional **Unified cost evidence** GitHub Actions workflow can be run manually,
or by pushing an exact source commit to a `verify/unified-cost-*` branch.

## Interpretation

Every case/variant has two separate arms. The baseline performs one exact
contraction without observers; the observed arm uses the existing CostLedger,
WorkTrace and `tracemalloc` observers. Each sample is a new Linux process.
Order alternates between repetitions. The result must match a pinned exact
fixture before becoming a valid timing observation. A worker refusal, timeout,
wrong count, incomplete cost ledger or missing arm makes the full experiment
fail; nothing is silently imputed. The complete report includes source and
verification fingerprints, git revision/dirty state, optional native binary
hashes, raw samples and summary medians.

**Time:** Duration excludes fixture construction and includes observer overhead
only in the observed arm. The ratio of median observed to median baseline
durations estimates the total instrumentation perturbation *for this workload*,
not an isolated causal or statistically rigorous overhead. It is not a solver
speedup or a CI performance regression threshold.

**Memory:** Linux `ru_maxrss` is the high-water RSS of the whole fresh process,
including interpreter, imports and allocator effects. `tracemalloc` tracks
Python allocations only, not native buffers. They are separate observations;
the peak of each may occur at a different instant.

**Cost:** A ledger counts recursive frames, per-frame ring calls, native-call
boundaries, phases, and aggregate counters. A WorkTrace observes eligible
operations and their inclusive durations. Never sum inclusive durations as
exclusive stage time. Ring method counts, estimated bytes and native-call
counts cannot be converted to bit operations without explicit operand-cost
bounds. The result deliberately has three top-level fields:
`measured`, `analytical`, and `unknown`.

The finite observed recursion tree can be reconciled, but no complete
worst-case bit-operation bound or universal non-refusal is claimed. The paper
schedule's activation threshold at practical input sizes remains an independent
research obstacle.

## Coverage boundaries

Current paired experiment covers the four ordinary recursive benchmark cases:
two partially conditioned 9x9 Sudoku fixtures (4 and 8 live wires), a parity
factor network and a nested two-wire factor network. It explicitly excludes
`crossing-4wire` because that case measures a deformation function rather
than a complete recursive contraction. This is **not** a realistic growing
Sudoku benchmark suite.

Native `packet`, `leaf` and `combined` variants are opt-in through
`--variants`; build and attest Cython before running them. The separate
native-cutover workflow remains the performance and equivalence study.

Next experimental extensions: (1) true growing Sudoku instances and explicit
refusals, (2) inclusive/exclusive frame and phase timing, (3) native operand
sizes, big-integer bit operations and allocations, (4) conditional recurrence
terms with independent upper-bound proofs. Do not widen the performance gate
until overhead and variance are characterized.
