# Exact Sudoku continuation rank: why residual-state merging stalls

**Scope:** A theorem about the *labelled full-solution indicator tensor*,
the obligation-signature frontier at a **fixed** cell cut, and the rank
of its prefix/suffix flattening. This is not a lower bound on the
runtime of every Sudoku counter or on a symmetry-quotiented count.

Executable small-instance evidence:
`reference/sudoku_continuation_rank.py` and
`tests/unit/test_sudoku_continuation_rank.py`.
The upstream structural-width result is in
[Sudoku frontier width](sudoku-frontier-width.md).

## 1. Finite-cut residual functions

Fix a Sudoku of side `n=b**2`, a complete order of its `N=n**2`
cells, and a cut after `k` cells. Let `P` be an assignment of
digits to the prefix cells and `Y` an assignment to the suffix cells,
both respecting the given clues where present. Define

```
H_k(P,Y) = 1 if concatenating P and Y is a legal completion;
           0 otherwise.
```

This is a finite, very large Boolean matrix, not a matrix we allocate.
Its row indexed by `P` is the **exact continuation function** of
`P`. Work over any field `F`: the entries 0 and 1 have their usual
interpretations.

A unit is *crossing* if it contains cells on both sides of the cut.
A *legal prefix* never repeats a digit in any row, column or box and
satisfies all prefix clues. Its **live signature** `sigma(P)` is
the set of used pairs `(unit,digit)` in crossing units only.
The number of prefix cells in a given crossing unit is fixed by
the cut, not by their assigned digits.

Write `S_k` for the set of signatures of legal prefixes that have
**at least one complete Sudoku extension**. A legal prefix with no
extension has the identically zero continuation row.

## 2. Exact theorem: rank equals extendable signature count

**Theorem.** For every Sudoku puzzle, every cell order, every cut, and
every coefficient field:

```
               rank_F(H_k) = |S_k|.
```

**Upper bound.** A suffix has internal constraints determined solely
by its own digit assignments. All constraints linking prefix and suffix
come from crossing units. For each such unit, compatibility means
that the suffix's used digits avoid precisely the prefix's live
`(unit,digit)` bits. Therefore two legal prefixes with the
same signature have the **same** continuation function. Illegal
prefixes and unextendable legal prefixes have zero rows. Hence there
are at most `|S_k|` distinct nonzero rows and
`rank_F(H_k) <= |S_k|`.

**Lower bound.** For each `s in S_k`, choose a prefix `P_s` and
a complete Sudoku witness whose suffix is `Y_s`. For a crossing
unit `U`, let `p_U` be its number of prefix cells. Since a
complete Sudoku uses every digit exactly once in `U`, the suffix
`Y_s` uses exactly the complement of the `p_U` digits
`sigma(P_s)` used there. Another legal prefix `P_t` occupies
exactly `p_U` distinct digits in `U`. To be compatible with
`Y_s`, all these digits must lie in the complement of the digits
used by the suffix, a set of cardinality `p_U`. Thus they must
be **equal** to those used by `P_s`, in every crossing unit.
Compatibility therefore forces `sigma(P_t)=s`.

For distinct `s,t`, `H_k(P_t,Y_s)=0`, whereas
`H_k(P_s,Y_s)=1`. The chosen rows and columns form a genuine
`|S_k| x |S_k|` **identity minor**, proving rank at least
`|S_k|` over *every* field.

The two bounds give equality. In particular, the nonzero
continuation rows from distinct extendable signatures have pairwise
disjoint support. There is **no exact equality-based merging** of
these signatures for all labelled future assignments. Nor can a
linear representation over a field of this full labelled indicator
tensor use a smaller bond at this cut.

Note the definition of `S_k`: this is the set of signatures
belonging to **some complete solution**, not every intermediate
signature the forward algorithm may visit. Dead reachable states
have a zero residual and may all be merged or pruned.

## 3. Symbolic non-polynomial rank witness after the first row

Consider an **empty** generalized Sudoku and the row-major cell
order. At cut `k=n` exactly the first row is processed.

A legal first row is one of the `n!` permutations of all
`n` digits. Every such permutation extends to a complete Sudoku:
take the canonical valid grid

```
d(r,c) = 1 + ((r*b + floor(r/b) + c) mod n)
```

with `r,c` zero-based, and globally relabel its digit alphabet.
Distinct first-row permutations produce distinct live signatures
because each column is crossing and records its assigned digit.
Thus `|S_n|=n!` and the theorem yields

```
        rank_F(H_n) = n!  (for an empty b^2 by b^2 Sudoku).
```

Examples: 4x4 rank 24; 9x9 rank 362,880; 16x16 rank
20,922,789,888,000. Stirling's approximation gives
`log2(n!)=Theta(n*log n)=Theta(sqrt(N)*log N)`, a
**superpolynomial** lower bound on a row-major *labelled*
tensor-train bond dimension. It is **not** `2**Omega(N)` and
is not a lower bound on all Sudoku counting algorithms or all
cell orders.

This is a genuine rank lower bound, unlike the earlier potential
frontier-width lower bound `W>=N`, which alone establishes
nothing about reachable signatures or ranks.

## 4. Independent finite checks: blank 4x4

Enumerating all 288 complete blank 4x4 grids independently,
extracting a live signature from each grid, and selecting one
complete-grid witness per distinct signature yields:

| Prefix cells | Potential live bits | Extendable signatures = exact rank | Digit-relabel orbits |
|---:|---:|---:|---:|
| 0 | 0 | 1 | 1 |
| 4 | 24 | 24 | 1 |
| 7 | 24 | 72 | 4 |
| 8 | 16 | 36 | 3 |
| 16 | 0 | 1 | 1 |

At cut 7, a full `72 x 72` matrix of **spliced witness**
acceptances is the identity, so the rank statement is checked
against the actual `Puzzle.valid_solution` implementation, not
against the equality of internal signature values alone.
At cut 8, two different prefixes with the same signature can
exchange their complete Sudoku suffixes without invalidating
the completed grid, checking the upper-bound direction.

For blank 4x4, the whole symmetric digit group `S_4`
preserves the puzzle and the row-major cut. At cut 7 the 72
labelled signatures fall into four orbits of sizes
`12,12,24,24`; at cut 8 the 36 signatures fall into three
orbits of sizes `6,6,24`.

**Important:** the rank remains 72 or 36, respectively.
Symmetry reduction counts orbits of an **equivariant family**;
it does not make the original labelled residual functions equal.
It can still accelerate a *symmetric aggregate count* because
suffix assignments may be relabelled along with prefix states.
This is exactly the distinction to respect when evaluating
`sudoku/symmetry.py` and `sudoku/weighted_zdd.py`.

## 5. Literature and implications for next refactor

- **Myhill–Nerode / residual languages.** The rows are exact residual
  acceptance functions. Deterministic state equivalence merges
  only equal residuals, not merely residuals with the same total count.
  See [an overview of residual languages](https://doi.org/10.1016/j.jlamp.2018.03.002).
- **Fliess/Hankel rank and weighted automata.** The rank of the
  prefix/suffix acceptance matrix controls a finite linear
  representation. See
  [Fliess' theorem for minimizing weighted automata](https://games-automata-play.github.io/blog/fliess_theorem/)
  and [Learning Weighted Automata](https://cs.nyu.edu/~mohri/pub/cai.pdf).
  This application is a finite **cell-cut** analogue; it does not
  require an infinite-string automaton construction.
- **Tensor-train ranks.** The minimum exact bond dimension for a
  fixed matricization equals its matrix rank; see Oseledets,
  *Tensor-Train Decomposition* (2011),
  [DOI 10.1137/090752286](https://doi.org/10.1137/090752286).
- **Communication complexity.** The selected
  prefix/suffix witnesses form an identity submatrix, a strong
  `fooling-set`-type witness. See
  [communication complexity notes](https://www.cs.toronto.edu/~toni/Courses/CommComplexity/Lectures/lecture1.pdf).

### Research decision

Do **not** invest in a generic 'merge equivalent continuation
signatures' pass for extendable Sudoku frontier states: the theorem
shows it cannot merge any two distinct labelled signatures.

Instead, focus on mechanisms whose promise is outside this theorem:
(1) exact **symmetry-orbit** aggregation with equivariant transitions,
(2) compact **symbolic descriptions** of exponentially many
independent labelled residual functions (e.g. structured tensor
circuits or ZDDs), and (3) direct computation of the single required
**total count** without exposing the full labelled suffix function.

Any asymptotic guarantee for those approaches must cover
construction, closure under every transition, coefficient bit
height, and worst-case work. Counting the four orbits in a 4x4
test is not an asymptotic certificate.
