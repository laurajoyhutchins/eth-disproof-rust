# Research objective: non-exponential exact Sudoku solving

## Precise goal to formalize

Develop and rigorously analyze an exact algorithm for a family of **generalized**
Sudoku instances whose size grows. A useful target is worst-case running time
`2^{o(N)}` up to polynomial factors, with `N` defined explicitly in a final
statement (for example, the input encoding length or number of cells).
This target is *subexponential*, not necessarily polynomial time.

An ordinary fixed 9×9 board has finitely many instances: timings on it alone
say nothing about `N -> infinity`. Input representation, puzzle generalization,
bit-operation cost, and whether the algorithm returns a witness, a count, or
a yes/no decision must all be explicit.

## What is implemented

- An exact recursive tensor-network contraction engine with separate schedules.
- Packet construction and bounded mode-state elimination.
- Exact arithmetic and coefficient recovery, with an explicit capacity policy.
- Independent small-instance oracles and Sudoku encoding checks.
- Measurement instrumentation for practical and structural work growth.

## What remains unproved

1. A proved reduction from generalized Sudoku to networks with the needed
   quantitative packing, degree and size invariants, with polynomial overhead.
2. All required recurrence hypotheses for **every** recursive instance, not
   only measured or specially constructed examples.
3. A bound on distinct states, child networks, intermediate polynomial terms,
   and coefficient bit lengths in the chosen parameter regime.
4. The total bit-operation cost of exact arithmetic, interpolation/recovery,
   mode elimination, and memoization (not only counts of high-level calls).
5. A recurrence solution yielding `2^{o(N)}` worst-case work for the complete
   algorithm under its declared resource limits, or a counterexample revealing
   which obligation fails.
6. A clear correctness theorem that proves no valid instance is incorrectly
   accepted/rejected and identifies exactly when a capacity refusal may occur.

## Empirical methodology

Use independent count oracles for correctness, retain failure/timeout/refusal
outcomes, characterize the largest intermediate states, and separate native
constant-factor improvements from changes to asymptotic complexity.

A claimed general non-exponential exact Sudoku algorithm would be a major
complexity-theoretic result. Claims should be supported by complete mathematical
proofs and independently reproducible verification, not performance plots alone.

## A known refusal boundary

The [bit-complexity audit](bit-complexity.md) supplies a real blank-4x4
Sudoku refusal under the literal schedule, a proof that edge count alone
cannot bound oracle work, exact operation-count bounds for direct leaf
evaluation and Newton interpolation, and vertex/precision path envelopes.
These rule out treating the existing recursion-count formula as a complete
non-refusing bit-time bound. The five obligations above are still open.
