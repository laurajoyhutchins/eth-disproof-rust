# Sudoku as a weighted exact-cover contraction

For a board of side `n = b²`, let `U` be the `3n` row, column and box units.
An allowed digit `d` in a cell `c` contributes precisely three obligations:

\[
 B(c,d)=\{(\operatorname{row}(c),d),
  (\operatorname{column}(c),d),
  (\operatorname{box}(c),d)\}.
\]

A complete filling is legal exactly when each cell contributes one choice
and no two chosen sets intersect. Therefore its exact count is

\[
 Z=\sum_{d_c\in D_c}\prod_{c\ne c'}
 [B(c,d_c)\cap B(c',d_{c'})=\varnothing].
\]

`state.py` computes deterministic singleton propagation and the obligation
masks. A supplied candidate domain is a **restriction**, not automatically
a count-preserving deduction. Conflicting singleton obligations imply zero.

## Frontier invariant

For any cell order, let `F_i` be the obligations that a future cell might
still use. After processing `i` cells, a dictionary maps a projected
occupied set `S ∩ F_i` to the **number of compatible prefix assignments**
with that projection. On every transition we reject overlaps, multiply by
integer multiplicity, and forget obligations outside the next future set.
The forgotten obligations cannot be used again; merging equal projected
keys therefore preserves exact counts. This does not bound frontier width
by a polynomial.

## Exact reductions

- **Components:** if the residual obligation-incidence graph splits into
disjoint connected components, their counts multiply. Adaptive conditioning
is a branching recurrence, not the forward-frontier algorithm.
- **Symmetry:** digit permutations are used only when all candidate domains
are preserved. A suffix-graph automorphism must also preserve the entire
remaining hypergraph, not just the next cell's choices.
- **Weighted ZDD:** a canonical diagram represents a finite map from
occupied-bit sets to nonnegative integer multiplicities. Diagram transitions
apply exact restriction, union, projection and addition.
- **Hybrid:** dictionary/ZDD conversions are validated representations of the
same finite weighted map. Preflight projections only guide the decision to
attempt conversion; they are not proofs of runtime complexity.

The counters separately impose state, operation, coefficient, and estimated
memory ceilings. Exceeding a ceiling is an **explicit refusal**, not a zero
count or evidence of an asymptotic theorem. Partial-prefix counts are labeled
as partial assignments, not full Sudoku completions.
