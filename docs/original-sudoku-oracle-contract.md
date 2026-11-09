# Original Sudoku entry-oracle cost contract

**Scope:** the direct bipartite Sudoku encoding from
`sudoku_network(Puzzle)`. This is **not** the different subcubic 3-CNF
reduction or the residual band encoding. It applies to the checked,
immutable `CellEntryOracle` and `UnitEntryOracle` programs, not arbitrary
Python callbacks.

## Exact source programs

For box order `b`, let `n=b²`, `N=n²` cells and
`t=max(1,ceil(log₂ n))` bits per digit. Each cell receives three `t`-bit
numbers, enforces equality, in-range and the optional clue; the unit gets
`n` encoded numbers and checks all-distinctness.

The canonical encoder no longer emits private nested Python closures. It
constructs frozen, slots-only callable objects with fixed source programs
and explicit `n,t,clue` fields. The new unit implementation uses an
integer bitset instead of `set(digits)`. No dictionary/hash complexity
assumption is required. The bitset spans at most

\[
2^t\le 2n
\]

bits. Importantly the *unit* does **not** separately enforce in-range
digits, matching the independent `DirectNetwork.local_entry`; the cell
entry does. This equivalence is tested exhaustively for representative
4×4 factors and with deterministic samples for 9×9 and 16×16, including
out-of-range local digit values.

For one original oracle invocation on a valid Boolean port tuple:

| | Cell entry | Unit entry |
|---|---:|---:|
| Boolean port checks (at most) | `3t` | `nt` |
| Decoded port bits (at most) | `3t` | `nt` |
| Shift/OR updates for decoding | `3t` | `nt` |
| Distinctness bitset updates | `0` | `n` |
| Maximum bitset width | `0` | `2^t` |
| Outer `ring.scalar` calls | `1` | `1` |

An explicit loose schoolbook **abstract bit-operation** envelope is
`64(3t+1)(t+1)²` for the cell Boolean work and
`64(nt+1)(t+2^t+1)²` for the unit Boolean work. This includes a coarse
allowance for bounded-width loop indices, integer shifts, comparisons,
bit tests and ORs. It is not an exact Python interpreter instruction
bound and does not cover runtime overhead or modified callbacks.

In the analyzed eager finite `Padic(e,p)` reference, the scalar input is
always `0` or `1` and the output has canonical `e*p` payload bits.
Charging `128(ep+1)²` per scalar as in the existing packet preparation
schoolbook model, one full pass over **all original tensor vertices** is
bounded by

\[
A(n,t,e,p)=
N\bigl(64(3t+1)(t+1)^2+128(ep+1)^2\bigr)
+3n\bigl(64(nt+1)(t+2^t+1)^2+128(ep+1)^2\bigr).
\]

For polynomial `e,p` this is polynomial in the number of input cells.

## Fail-closed correspondence

`reference/sudoku_oracle_cost.py` reconstructs *every* expected cell
port and row/column/box unit port directly from the puzzle and demands
exact topology, names, clues and callable classes. Any generic `lambda`,
forged immutable-oracle fields, foreign port map or modified clue is
rejected rather than assigned an unjustified zero cost. The tests retain
the original direct-network evaluator as an independent semantic oracle.

`assemble_paper_recurrence(..., original_sudoku=(puzzle, network))`
can attach this verified one-pass work and scalar-call count. It checks
matching root edges, vertices and input name bits, and requires precision
of at least `N*t+1` to represent any exact Sudoku completion count.

**A one-pass cost is not a whole-frame cost.** The current theorem still
needs a source-correspondence bound on every invocation of an inherited
original oracle across deformation centers, factor projections, terminals,
and recursive child evaluations. New `PacketEntry` callbacks and native
kernels require their own closure lemmas. As a result, no open theorem
premise is removed, and the deliberately failing research acceptance
test remains failing. Nothing here establishes non-refusal or
`2^{o(N)}` for Sudoku cells.

Run:

```bash
PYTHONPATH=src:. python -m pytest -q tests/contracts/test_sudoku_original_oracle_contract.py
PYTHONPATH=src:. python -m mypy --strict --no-incremental
```
