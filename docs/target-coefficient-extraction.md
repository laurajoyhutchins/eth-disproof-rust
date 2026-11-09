# Target coefficient extraction without global expansion

**Status:** exact, differential-tested *research implementation*, not enabled
as the default `PacketEntry` evaluator. It preserves the production
Python/Cython/lazy dispatch decisions. It does **not** prove a
non-exponential worst-case Sudoku algorithm.

## Which intermediate objects are unnecessary?

A prepared packet's non-tile coefficient update computes

\[
 [x_1^{\beta_1}\cdots x_k^{\beta_k}]
 \prod_{j=1}^{r}\left(c_j+\sum_{i\in S_j}a_{ji}x_i\right).
\]

The existing eager Python implementation materializes an exponent-tuple
dictionary after every row, including keys that can **never reach**
the requested target `beta` with the remaining rows.

`reference/target_coefficient.py` implements two exact transformations:

1. **Incidence factorization.** Form the bipartite graph of rows and target
   modes with nonzero desired exponent. A row containing several mode terms
   connects those modes. Separate connected components depend on disjoint
   variable sets; their target coefficients multiply. Constant-only rows
   multiply as scalars. Terms in variables with requested exponent zero
   are dropped *before* any coefficient computation.
2. **Future-row feasibility.** After processing row `j`, retain a partial
   exponent `alpha` only if
   `sum(beta-alpha)<=remaining_rows` and, for each mode `i`,
   `beta_i-alpha_i<=remaining_rows_offering_mode_i`.
   Each future row contributes at most one target-mode exponent, so
   either failure proves the partial state cannot contribute to the
   requested coefficient. This test runs before ring operations or
   creating the new dictionary entry.

Both operations are equalities of exact coefficients in the commutative
finite `Padic`/nested `JetRing` used by the solver. No coefficient
approximation, probabilistic pruning or numerical threshold is used.

## Independent verification

`tests/unit/test_target_coefficient.py` compares the new extractor with:

- The existing unpruned forward exponent expansion, represented
  independently as a small reference.
- Direct exhaustive selection of one affine term from each row, on
  deterministic random polynomials in Padic and nested JetRing rings.
- Real `PacketEntry._evaluate_python` outputs at multiple precisions,
  target multiplicities, groups, and *every* Boolean port assignment in
  the small cross-mode fixture.

The tests include target-zero variables, absent required modes,
constant-only rows, repeated mode terms, negative coefficients,
disconnected components, and one connected cycle. Native packet kernels
and lazy expression DAGs are rejected; they need independent equivalence
and performance evidence.

## What happened in the controlled experiment?

The reproducible study is

```bash
python -m benchmarks.packet_target_extraction --repeats 3
```

Its first GitHub Actions run on Python 3.13 measured the following exact
**peak dictionary state counts** (not bytes or bit operations):

| Synthetic family | Target modes | Forward peak | Pruned/component peak |
|---|---:|---:|---:|
| Independent affine factors | 12 | 4,096 | 1 |
| One connected sparse cycle | 12 | 4,096 | 2 |
| Four disconnected three-mode blocks | 12 | 4,096 | 3 |
| Complete dense permanent | 8 | 256 | 70 |

All computed coefficients were equal. The study also provides
same-process observational timings, but there are too few repetitions,
no independent process isolation, and insufficient real packet-family
coverage to claim a production speedup. No dispatch decision depends on
these timings.

**The examples are constructed polynomials, not proof that the literal
paper-Sudoku packet construction can produce the same geometry.** The
benchmark separately checks one real prepared cross-mode fixture;
that small fixture is a correctness test, not an asymptotic scaling
regime.

## Why some exponential behavior survives

If there are `k` rows and `k` target modes, every row can offer every
mode, and all constants are zero, then the target coefficient is

\[
 [x_1\cdots x_k]\prod_{r=1}^k\sum_{i=1}^k a_{ri}x_i
 =\operatorname{perm}(A).
\]

The target can have a short representation and still require hard exact
coefficient extraction. In this dense connected family, the suffix
test reduces the peak state set from `2**k` to roughly the central
binomial coefficient, which remains exponential.

A source-level crude bound on working dictionary space is proportional to

\[
 \max_C\prod_{i\in C}(\beta_i+1),
\]

where `C` ranges over connected row-mode components, rather than the
product over *all* modes. Suffix feasibility can improve this further.
Time also includes scanning the factors and available terms, hashing
exponent keys and finite-ring arithmetic. The implementation does not
yet have a complete worst-case bit-cost or native allocation bound.

## Next falsifiable question

Measure the **incidence graph structure of actual paper-admitted packet
families** as input size and residual difficulty grow. If mode
connectivity stays narrow, decomposition or more general variable
elimination can eliminate most unnecessary coefficient states.
If it becomes dense and entangled, merely changing the expansion
direction will not establish non-exponential worst-case work.

Do not replace the default evaluator until representative native and
Python comparisons establish both equivalence and improved performance.
The intentionally red worst-case theorem acceptance test stays red.
