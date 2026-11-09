# Constructive elimination orders and worst-case representation size

**Claim status:** exact structural theorems for two specified representations.
Neither is a proof of subexponential worst-case exact Sudoku time in the
number of cells, nor a lower bound on the cost of all compressed algorithms.

The executable certificates are `reference/sudoku_frontier_width.py` and
`reference/elimination_width.py`. Both avoid allocating factors or
enumerating candidate assignments. Their formulas, hypotheses, and
counterexamples are tested in
`tests/unit/test_structural_width_certificates.py`.

## 1. The quantity an order can control

Given finite factors `f_a(x_{S_a})`, domains of sizes `d_v`, and a
specified elimination order, put `B_v` for the union of the scopes of
factors incident to the next variable `v`, including `v` itself.
Dense bucket elimination needs at most

```
joined assignments at step v = product(d_u for u in B_v)
output entries at step v = product(d_u for u in B_v minus {v})
```

assignment **slots** for that step. Include original factor sizes in the
bound. For `m` factors and `g` variables, the maximum dense table size
is `max_a product_{v in S_a} d_v` or the maximum newly joined/output
scope product, whichever is larger. The conservative total number of
slots created is at most the sum of original factor sizes and the
output-size bounds for each elimination step. The total joined domain
volume bounds assignment iterations for a reference implementation
that scans dense buckets.

This bound applies also to a sparse factor representation that retains
at most one coefficient per assignment, **but does not predict whether
its support is much smaller**. A table entry may contain a jet with
many coefficients, a huge rational, a 2-adic extension element, or a
reference to an expensive local oracle. The number of slots is neither
a process-RSS bound nor a bit-operation theorem.

For domains `d_v <= d` and a primal graph with a supplied
tree decomposition of width `w`, a corresponding elimination order
has joined scopes of at most `w+1` variables. Thus exact dense
bucket elimination uses `O(poly(m,g) * d**(w+1))` coefficient
operations and `O((m+g) * d**(w+1))` stored slots (crude bounds).
**This is a conditional, standard treewidth guarantee**, not a promise
that arbitrary instances have small `w` or cheap coefficient arithmetic.

### Explicit polynomial family: pairwise forests

For a primal interaction graph that is a forest and factors with at
most two variables, repeatedly eliminate a leaf (including isolated
vertices). Its only remaining neighbor forms at most a two-variable
joined bucket. This is an algorithmically constructed order, not an
assumed optimal oracle.

If there are `g` groups, each holding at most `s` Boolean variables,
each group domain has size at most `d=2**s`; each joined table has
at most `d**2=2**(2s)` slots and each resulting message at most
`d` slots. The number of arithmetic operations required by a
straightforward dense implementation is polynomial in `g` times
`2**(2s)`, assuming each coefficient operation has bounded cost.
For constant `s` this is linear up to a polynomial factor; for
`s=O(log g)` it is polynomial in `g`.

This covers the structural family in
`benchmarks/eth/factorized_taylor_probe.py`, whose groups each have
two Boolean variables and whose primal interaction graph is a chain.
For this family the constructive certificate bounds each joined
domain by `4**2=16` possibilities. The implementation's reported
maximum factor entries of 12 is an observed, smaller sparse quantity.

### Obstruction: clique interactions

For pairwise factors on the complete graph `K_g`, every elimination
order starts with a variable interacting with all the others, so its
first joined bucket includes all `g` groups. The **structural**
dense-domain bound is `d**g`, whatever the order. In
`docs/eth.md`, an independently certified ETH measurement-design
family has such a complete group graph despite few measurement rows.

This does **not** prove that all exact counting algorithms require
`d**g` work. Those factors may admit sparse, low-rank, symmetric,
or otherwise compact representations. It disproves only a general
claim that *ordering alone* bounds their dense-table width.

## 2. A constructive and nearly width-optimal Sudoku order

Let Sudoku box order be `b>=2`, side `n=b**2`, and `N=n**2=b**4`
cells. An empty board has `3n` row, column and box units, each with
`n` unit-digit obligations. The obligation-frontier algorithm records
which used obligations might conflict with a future cell.

Fix a cell order. Call a unit **mixed** at cut `k` if it has at least
one cell among the first `k` and at least one among the remaining
`N-k`. On an empty board, every digit is allowed in every cell, so
each mixed unit contributes exactly `n` distinct *potentially live*
obligations to the structural frontier. Consequently,

```
W(order) = n * max_cut(number of mixed row/column/box units).
```

This is the structural dimension of the obligation-mask space,
not the logarithm of the number of **reachable** masks.

### Theorem A (constructive upper bound)

In row-major cell order, at any cut:
- at most one row is mixed;
- at most `n` columns are mixed;
- at most `b` boxes are mixed, all in the current box band.

Thus `W <= n*(n+b+1)`. At cut `k=n+1`, the first row has
been completed and one cell of the second row has been processed.
All `n` columns, all `b` boxes of the first band, and the second
row are mixed (for `b>=2`), so equality holds:

```
W(row-major) = n**2 + b*n + n
             = N + N**(3/4) + sqrt(N).
```

This holds for every blank generalized Sudoku size in the family,
not merely for the sample sizes tested.

### Theorem B (lower bound for *every* cell order)

Take the cut after `floor(N/2)` cells, and let `r` be the number of
mixed rows and `c` the number of mixed columns. We claim `r+c>=n`.

Suppose instead `r+c<n`. At least one row and at least one column
are nonmixed: each is entirely processed or entirely unprocessed.
There cannot be both a completely processed and a completely
unprocessed row, because then **every** column would be mixed,
forcing `c=n`. The analogous statement holds for columns.
Moreover, a nonmixed row and nonmixed column must agree on whether
they are processed, since their intersection is one cell.

Therefore all nonmixed rows and columns have the same status.
If they are unprocessed, all processed cells lie in the
intersection of the `r` mixed rows and `c` mixed columns.
If they are processed, all unprocessed cells lie there instead.
In either case at least `floor(N/2)` cells fit inside an
`r x c` rectangle. But

```
r*c <= (r+c)**2 / 4 < n**2 / 4 = N / 4
                          < floor(N/2),   for n>=4.
```

Contradiction. Thus `r+c>=n`, which gives at least `n**2=N`
potentially live row/column obligation bits at that cut, even
without counting boxes:

```
W(any cell order) >= N.
```

Combining the two theorems:

```
N <= min_order W(order) <= N + N**(3/4) + sqrt(N).
```

Therefore the **best structural obligation frontier width** is
`N + o(N)`. No ordering of the original cells alone makes that
structural width sublinear in the number of cells.

### What this does, and does not, bound

At every layer of the row-major *unbounded* exact-cover dynamic
program, all counts share any fixed-given obligation mask. Only
obligations used by earlier **free** choices and available to later
free choices can vary. Restricting candidate domains cannot add
new varying bits beyond the blank-board geometry. Hence the number
of distinct projected signature keys at a layer is at most

```
2**(N + N**(3/4) + sqrt(N)).
```

There are `N` cells and at most `n` choices per cell; counts of
prefix completions have at most `N*ceil(log2(n))+1` bits. An
abstract exact dynamic program with polynomial-cost bitset and
integer operations consequently admits a **uniform**
`poly(N) * 2**(N+O(N**(3/4)))` bit-operation upper bound,
provided it is allowed enough space to complete.

This is an explicit asymptotic improvement over enumerating
`n**N=2**(Theta(N*log N))` cell assignments. However:

1. It is **still exponential in the number of cells** `N`, and
   does not establish `2**o(N)`, polynomial time, or a refutation of
   ETH. Subexponential in the larger dense-input encoding length
   is a different statement from subexponential in cells.
2. The lower bound `W>=N` is on **structural potential bits**.
   It does **not** imply `2**N` reachable frontier states, a
   tensor-rank lower bound, or an intrinsic computation lower bound.
   Exact-cover consistency, ZDDs, group actions and other algebraic
   compressions could require drastically fewer states.
3. The current `sudoku/frontier.py` implementation has **finite
   state/transition/memory caps and can refuse**. The unconditional
   asymptotic counting bound refers to its uncapped mathematical
   dynamic-programming recurrence, not the current configured
   runnable implementation's totality or Python dictionary timing.
4. The direct Boolean tensor network in `sudoku/direct_network.py`
   is a **different representation**. Its raw `n*ceil(log2 n)`-bit
   unit oracles are not made small by the above obligation frontier
   result. Similarly, one Sudoku unit's exact subset-cut rank does
   not certify a global contraction ordering.

## 3. Concrete structural certificates

| Box order `b` | Side `n` | Cells `N` | Every order `W>=` | Row-major exact `W` | Formal state-map bound |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 16 | 16 | 28 | `2**28` |
| 3 | 9 | 81 | 81 | 117 | `2**117` |
| 4 | 16 | 256 | 256 | 336 | `2**336` |
| 5 | 25 | 625 | 625 | 775 | `2**775` |
| 6 | 36 | 1296 | 1296 | 1548 | `2**1548` |

The table is mathematical upper/lower **structural** evidence, not
measured runtime or memory. The implementation computes width by
tracking exactly which units straddle each cut; it does not construct
a dense state map or a solution table.

## 4. What should be researched next

The structural-ordering question is now resolved within these
representations: cheap orders exist for bounded-width interaction
families; row-major is asymptotically width-optimal for the full
Sudoku obligation frontier; and certain ETH group-factor graphs
admit no low-width order at all.

A follow-on theorem is now proved in
[Sudoku continuation rank](sudoku-continuation-rank.md): at every cut,
the **exact rank** of the labelled full-solution prefix/suffix matrix
equals the number of extendable frontier signatures. Thus distinct
extendable signatures have disjoint continuation languages, and at
the first row of a blank Sudoku the row-major tensor bond rank is
exactly `n!`. This is a rank obstruction for that representation,
not a general runtime lower bound; symmetry aggregation and implicit
symbolic contraction remain separate possibilities.

The remaining research question is **representation-aware width**:
can a certified transformation maintain smaller *reachable supports*,
exact quotient states, low-rank tensor bonds, or bounded-size
polynomial circuits *through every elimination step*, even when
the structural scope contains `Theta(N)` obligations? Any proposed
bound must account for coefficient bit heights, conversion costs,
and closure under subsequent contractions.

Useful foundations: Dechter, *Bucket Elimination: A Unifying Framework
for Reasoning* (1999), DOI 10.1016/S0004-3702(99)00059-4; Aji and
McEliece, *The Generalized Distributive Law* (2000),
DOI 10.1109/18.825794; Oseledets, *Tensor-Train Decomposition*
(2011), DOI 10.1137/090752286.
