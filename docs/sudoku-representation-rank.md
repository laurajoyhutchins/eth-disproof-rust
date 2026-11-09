# Sudoku representation audit: factor width and exact subset rank

The purpose is to distinguish **mathematically compact tensor
descriptions** from the cost of actually contracting them. This audit
inspects the *canonical*, parsimonious direct Sudoku input, without
using clues to pin wires or precompute Sudoku solutions.

## Width obstruction

For box order `b`, Sudoku side `n=b²`, and digit bit width
`t=ceil(log2(n))`, the canonical direct tensor network has
`M=3*n²*t` Boolean wires. Every one of the `3n` row/column/box
unit tensors has `n*t` Boolean inputs. The lifted direct-packet
representation doubles the network to `2M` Boolean variables, and
carries those same unit tensors into its initial factor tables.

| Board | Original M | Lifted 2M | Unit input arity | Raw unit table entries |
|---|---:|---:|---:|---:|
| 4×4 | 96 | 192 | 8 | 2^8 |
| 9×9 | 972 | 1,944 | 36 | 2^36 |
| 16×16 | 3,072 | 6,144 | 64 | 2^64 |
| 25×25 | 9,375 | 18,750 | 125 | 2^125 |

An input table with `n*t` variables already exceeds the default
`max_width=16` on 9×9 and larger. This is a **necessary factor
width lower bound for the current implementation** regardless of how
packets are arranged. It is not an exact treewidth result, and it
does not prove that a different factorization cannot be efficient.

## Rank theorem for one Sudoku unit

The raw canonical `UnitEntryOracle` enforces only that `n`
`t`-bit codes are distinct, and can accept codes `>=n` when
`n` is not a power of two. Each adjacent `CellEntryOracle`
forces the corresponding digit to the legal range `0,...,n-1`.
The valid-digit restriction is thus exact on globally supported
assignments, **not identical as an isolated raw unit tensor**.

Split a valid-digit unit into `k` digit variables and `n-k`
digit variables. Write `S` for the set used on the first side.
The all-different indicator factors as

\[
U(d_1,\ldots,d_n)=\sum_{S\subseteq[n],\,|S|=k}
\mathbf{1}[\{d_1,\ldots,d_k\}=S\text{ with no repetition}]
\mathbf{1}[\{d_{k+1},\ldots,d_n\}=[n]\setminus S
\text{ with no repetition}].
\]

This gives a rank upper bound `C(n,k)`. Conversely, pick one
canonical permutation for every `k`-subset on the first side, and
the canonical complementary permutation on the second. Those
selected rows and columns form an **identity matrix**, proving
the same rank lower bound over every field. Thus the rank of the
restricted unit matricization is exactly `C(n,k)`.

| Board | Balanced cut | Exact restricted rank / raw-rank lower bound |
|---|---:|---:|
| 4×4 | 2 / 2 | 6 |
| 9×9 | 4 / 5 | 126 |
| 16×16 | 8 / 8 | 12,870 |
| 25×25 | 12 / 13 | 5,200,300 |

The reference implementation evaluates subset factors **without**
enumerating all subsets, and the tests independently compute the full
4×4 unit's Boolean matrix rank over GF(2) to confirm the theorem
on actual source oracles. For 9×9, an invalid digit is accepted by
the standalone raw unit but rejected by its cell oracle, protecting
the semantic distinction.

**Interpretation.** A compact valid-digit unit tensor can use
complement-subset states rather than a dense `2^(n*t)` table.
But the necessary midpoint rank still grows combinatorially in
`n`. Rank of one isolated tensor is *neither* a bound on the
global row/column/box network contraction *nor* a worst-case
Sudoku hardness theorem.

## Mode-vs-packet comparison

`benchmarks.sudoku_representation_audit` also constructs the
repository's actual `r=64, a=2` Cauchy packets, validates slot
orientation and uses an **independent arithmetic projection** of
the `t=1` mode catalog. It reports the exact count of mode
descriptors at root precision `M+1` and a binary support lower
bound for mode assignments, without constructing mode tables or
coefficient arrays. The latter is **not** an operation lower bound:
a sufficiently clever symbolic elimination may avoid enumerating
those assignments.

Use:

```bash
python -m benchmarks.sudoku_representation_audit --boxes 2 3 4 --packing \
  --output artifacts/sudoku-representation.json
```

The workflow `Sudoku representation certificates` preserves the
source-pinned JSON. Do not infer an exact induced width, runtime
speedup, or polynomial complexity from these structural certificates.

Crucially, **givens do not change the original tensor incidence
graph**; clues change cell-oracle values. Consequently, this structural
audit alone cannot distinguish an empty puzzle from a hard one.
Any future reduction that uses clues must explicitly record the
new reduced network, prove exact equivalence and audit *that*
network separately.
