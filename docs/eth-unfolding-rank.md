# Exact contraction rank: a falsifiable invariant and its obstruction

This note separates **a genuine representation lower bound** from
**computational complexity of exact #SAT**. It applies to the rational
deformation polynomial of `eth.polynomial` at one fixed rational
interpolation parameter. It is *not* a theorem about the paper's full
sparsification schedule, truncated jets, or generalized Sudoku.

## The exact invariant for a specified cut

For a Boolean assignment tensor `f : {0,1}^n -> Q` and partition
`A | B`, form the `2^|A| x 2^|B|` unfolding
`M[a,b] = f(a,b)`. Its exact rational matrix rank is the minimal
number `D` of separated terms in an identity

```
f(a,b) = sum_{j=1}^D g_j(a)*h_j(b).
```

One direction follows because each outer product has rank at most
one. The reverse direction follows from an exact rank factorization
of `M`. Consequently, any exact **tensor-train / MPS along a fixed
variable order** needs bond dimension at least the unfolding rank
at every prefix cut. The ranks are achievable as tensor-train ranks
with ordinary exact linear algebra, although calculating them from
explicit matrices may itself be exponential.

This is standard matrix-rank algebra, closely connected to Oseledets,
*Tensor-Train Decomposition*, SIAM J. Sci. Comput. 33 (2011),
Theorem 2.1, DOI: https://doi.org/10.1137/090752286.

The executable oracle `eth.unfolding_rank` deliberately enumerates
the full Boolean cube and computes exact Fraction Gaussian rank.
It checks all replacement identities at `T=0`, limits matrix
cells, rational operations and coefficient bit lengths, and records
the input formula's deformed sum. It is a **measurement oracle**;
the production CNF/Taylor solver does not invoke it.

## Proven counterexample to a naive universal small-rank invariant

Take `n=2k` declared variables
`x_1,...,x_k, y_1,...,y_k` and the width-one CNF

```
F = x_1 AND ... AND x_k.
```

For occurrence `i` use the polynomial replacement
`P_i(T,x,y)=x_i+T*y_i`. The identity-at-zero contract holds
because `P_i(0,x,y)=x_i`. The deformed assignment function is

```
H_T(x,y) = product_i (x_i+T*y_i).
```

At `T=0`, the x-versus-y unfolding has rank **1**.
For nonzero `T`, the unfolding is a Kronecker product of `k`
two-by-two blocks

```
[ 0   T   ]
[ 1  1+T  ]
```

whose determinant is `-T`. Therefore its rank is exactly
`2**k`, with no numerical approximation or asymptotic extrapolation.
The full Boolean sum is nevertheless easy:

```
sum_{x,y} H_T(x,y) = (2+2*T)**k.
```

So an exponential rank across **one prescribed cut** is **not**
a #SAT lower bound. A variable order grouping all x's before all y's
has maximum exact tensor-train rank `2**k`, while interleaving
`x_1,y_1,x_2,y_2,...` has maximum rank only **2**.
The same exact function exposes why *ordering matters*. The algebra
is independently checked for small `k` by the bounded rank oracle,
but the identity itself holds for every positive integer `k`.

This disproves any universal bounded-rank assertion obtained
**solely** from bounded clause width and identity-at-zero replacement
conditions. The example's replacements are valid under
`ReplacementSystem.validate`, but they are **not asserted to be**
the specific spectral/measurement construction in the paper.

## Exhaustive best-order rank, not just a convenient cut

For a fixed `n`-variable tensor, define `r(S)` as the exact rank
of the unfolding `S | complement(S)`. This depends only on the
subset `S`, not on the order of variables within the sides.
The minimum possible maximum tensor-train bond dimension over **all
variable permutations** is exactly computed, for small bounded `n`,
by subset dynamic programming:

```
B(empty) = 1
B(S) = min_{v in S} max(B(S-{v}), r(S))   for proper nonempty S
B(all) = min_{v in all} B(all-{v})
```

The proof is induction on the prefix subset. Every permutation of
`S` has some last variable `v`. The previous prefixes lie entirely
inside `S-{v}`, so the largest encountered bond rank is at least
`max(B(S-{v}),r(S))`. Appending `v` to an optimal prefix ordering
achieves that maximum. The final full-set boundary is not an internal
bond. Repeatedly minimizing proves optimality over all variable orders.

`minimax_unfolding_order` checks all `2**n-2` proper nonempty
subsets with an explicit `max_cuts` budget and exact rational ranks.
It reconstructs a certifiably optimal variable ordering. This is an
**exponential diagnostic**, not a polynomial algorithm for finding
such orderings in general. For the crossing-pair witness, exact
exhaustive minimax is 2 even though the grouped order requires
`2**k` at its middle cut. This shows that the first obstruction
is specifically **ordering-sensitive**.

The source-pinned experiment also computes exact minimax profiles
for the repository's real n=3 and n=4 constructed path CNFs at their
certified interpolation centers. Each independently checked rank
profile constrains *one center's assignment tensor only*.

## A safe support-based upper bound on each cut

Compute the set of Boolean variables with nonzero replacement
coefficients evaluated at a center for every clause. A clause
crossing the cut may involve sets `A_boundary` and `B_boundary`
on either side. Local-only clause factors can be absorbed into
functions of `a` or `b`, leaving the crossing product dependent
on only those boundary variables. Thus

```
rank_Q(M) <= 2 ** min(|A_boundary|, |B_boundary|)
```

for *every* such factorization. The code computes this upper
bound independently of Gaussian elimination and fails if the
measured rank exceeds it. It can be loose: exact cancellations
or special spectral identities may lower the true rank.

For a path CNF under the natural variable order, the boundary
contains at most one variable on each side, giving a rank-at-most-2
certificate. For the grouped crossing-pair example, the bound is
`2**k` and is attained at every nonzero `T`.

## Source-pinned first measurements of the certified construction

The source-pinned
[CNF rank run](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42710068603)
at commit `cebd89107de04ae635c2b4d0dd92cb9ff2ed8a17`
completed all its bounded exact rank and full-pipeline checks.

The grouped `x|y` crossing-pair ranks at `T=1` were
`2,4,8,16` for `k=1,2,3,4`. The interleaved orders had maximum
rank `2` throughout, and exhaustive best-order search confirmed
optimum `2` for `k<=3` (up to 62 separate subset cuts).

For the **actual, certified** `r=Q=R=2` construction on path
CNFs, the exact Q-rank profiles in natural variable order were:

| Input CNF | Center | Natural rank profile | Exact best-order peak | Sum of deformed tensor |
| --- | ---: | --- | ---: | ---: |
| path n=3 | 1 | 2, 1 | 2 | 3 |
| path n=3 | 2 | 2, 2 | 2 | 1 |
| path n=4 | 1 | 2, 1, 1 | 2 | 3 |
| path n=4 | 2 | 2, 2, 1 | 2 | -1 |

The factor-support boundary upper bounds were **tight** for every
reported cut. Every tensor sum agreed with an independently
constructed whole deformation polynomial `H(T)`; evaluating at
`T=0` gives the original exact counts (5 and 8, respectively).
A nonzero-center deformation sum can be negative and is **not** a
Boolean model count. These small observations do **not** establish
that path-family ranks stay bounded at growing n, or that the actual
construction admits a cheap rank factorization.

The raw evidence is retained in the
[cnf-unfolding-rank artifact](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42710068603/artifacts/13716020846).

## What this proves and does not prove

- **Proved:** A precise, representation-invariant cut rank for
  separated linear representations and its sufficient exact
  factor-support upper bound.
- **Proved obstruction:** Width-one source clauses plus valid
  identity-at-zero replacements do **not** force small ranks for
  an arbitrary fixed variable cut.
- **Demonstrated escape:** Merely reordering variables can drop
  exponential maximum tensor-train rank to 2 for that witness.
- **Measured, not extrapolated:** Exact rank profiles and optimal
  variable-order profiles for small instances of the repository's actual constructed replacement
  systems at their certified interpolation centers.
- **Not established:** Any uniform rank bound for the *actual*
  paper construction across growing input families; small
  bond dimensions for every order; polynomial bit cost for finding
  a good order; a bound for truncated Taylor jets or all centers;
  a non-refusing subexponential exact counting algorithm.

This experiment is complementary to the support-join and dense
bucket research in PR #51 and the Sudoku subset-rank work in #55.
Sparse monomial support, small factor width and small exact
unfolding rank are **different invariants**; none implies the
others without additional assumptions. The next viable proof
obligation is to identify a uniform structural property of the
*certified spectral replacements* that bounds either a suitable
sequence of unfolding ranks or the cost of a different contraction
representation, including its coefficient bit growth.

## Reproduce

```bash
python -m pytest -q -m checkpoint tests/eth/test_unfolding_rank.py
python -m pytest -q -m integration tests/eth/test_unfolding_rank.py
python -m benchmarks.eth.unfolding_rank \
    --max-pairs 4 --output artifacts/eth-unfolding-rank.json
```

The source-pinned CNF scaling workflow runs this bounded diagnostic
and archives separate JSON. A `complete` result means all requested
rank *oracle* calls and checks completed, **not** that the
production algorithm can count every instance.
