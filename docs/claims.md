# Claims and proof boundaries

| Statement | Scope | How it is checked |
| --- | --- | --- |
| Coefficient operations are exact | Declared finite 2-adic quotient rings | Ring identities and independent small references |
| Sudoku frontier transitions preserve counts | Given candidate-domain restrictions, until explicit capacity refusal | Inductive frontier invariant and independent exact-count fixtures |
| Residual components factor | No shared live obligations | Graph partition and exact product comparisons |
| Symmetry quotient preserves counts | Only certified domain or remaining-graph automorphisms | Generator certification and unquotiented comparisons |
| ZDD/hybrid compression is count-preserving | Completed exact conversions, with capacity limits | Differential tests against dictionary frontier and independent counters |
| CNF reductions are parsimonious with tracked free-bit factors | Declared-variable semantics | Small brute force and optional Ganak |
| Recursive contraction agrees with direct counts | Executed, admitted instances | Independent truth tables, witnesses, and oracles |
| Worst-case subexponential generalized Sudoku algorithm | **Not established** | Missing complete non-refusing bit-operation recurrence |

## Established Sudoku width and rank results

This is the **single inventory** for these claims. Detailed proofs stay in
their existing documents; independent tests remain beside their respective
reference implementations. A green test verifies a bounded witness or proof
calculation, not an asymptotic theorem by itself.

| Result | Hypotheses and exact conclusion | Proof / independent evidence | Dependency and boundary |
| --- | --- | --- | --- |
| **Unit subset rank** ([PR #55](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/55)) | A single all-different unit with **valid** digits `0..n-1`, split after `k` positions, has rank `C(n,k)` over every field. | [Unit proof](sudoku-representation-rank.md), `reference/sudoku_unit_rank.py`, `tests/unit/test_sudoku_representation_rank.py`. | Foundational complement-of-used-digits lemma. The raw `UnitEntryOracle` may accept out-of-range binary codes: the equality holds **after** the cell-imposed valid-digit restriction. Not a global rank bound. |
| **Frontier structural width** ([PR #76](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/76)) | Empty generalized Sudoku of `N=n²` cells, row-major obligation frontier: width exactly `N + N^(3/4) + sqrt(N)`. Every cell order has potential width at least `N`. | [Width proof](sudoku-frontier-width.md), `reference/sudoku_frontier_width.py`, `tests/unit/test_structural_width_certificates.py`. | Measures **potential** live obligation bits, not the number of reachable states, tensor rank, or a lower bound on runtime. |
| **Global continuation rank** ([PR #83](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/83)) | **Any** Sudoku puzzle, fixed cell order and cut: rank over every field of the labelled full-solution prefix/suffix indicator matrix equals the number of **extendable** crossing-unit obligation signatures. | [Continuation proof](sudoku-continuation-rank.md), `reference/sudoku_continuation_rank.py`, `tests/unit/test_sudoku_continuation_rank.py`. | Extends the **complement condition** of PR #55 across all crossing units and adds full-grid witness selection. Does **not** follow from the numerical formula `C(n,k)` alone. Dead reachable states give zero rows. |
| **First-row rank** (corollary of PR #83) | Empty side-`n` Sudoku, **row-major cut immediately after row one**: exact labelled rank `n!`. | Same [continuation proof](sudoku-continuation-rank.md) and `exact_first_row_rank` tests. | Every first-row permutation extends by global digit relabelling. This is a fixed-cut tensor-bond obstruction, not a bound for other orders or for counting the final scalar. |

**What remains open:** No uniform polynomial or `2^o(N)` **bit-operation**
bound has been established for generalized Sudoku counting. The global rank
theorem rules out identifying *distinct extendable labelled signatures* by
identical continuation functions; it does **not** rule out symmetry-orbit
aggregation, ZDDs, implicit circuits, or direct scalar evaluation. The
observed 4x4 reduction from 72 labelled signatures to four digit orbits is
finite-size evidence, not a worst-case orbit-count bound.

**Before proving another width/rank result:** check this inventory and the
linked hypotheses. Distinguish **unit** from **global** tensors, **potential**
from **extendable** states, labelled ranks from **symmetry quotients**, and
matrix ranks from **runtime/bit complexity**. Extend an existing result
instead of restating its proof as an independent discovery.

The resource ledgers are accounting models, not automatically resident-set
memory bounds. Fixed-board benchmarks are measurements, not asymptotic
complexity results. Return states distinguish exact zero, explicit unsupported
configuration, and capacity refusal. See also `paper-admissibility.md`,
`bit-complexity.md`, `recurrence.md`, and `packing-proof.md`.
