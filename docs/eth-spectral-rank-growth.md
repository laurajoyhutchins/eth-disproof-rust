# Uniform spectral-support rank: a structural test, not a worst-case proof

## The lemma

Take the exact Boolean deformation

```
F_T(x) = product_e [1 - product_{literal in e} false_l(
    sum_v P_{e,l,v}(T)*x_v
)]
```

where each coefficient `P_{e,l,v}(T)` is a rational polynomial.
For a fixed cut of Boolean variables `L | R`, the **polynomial
support hyperedge** of clause `e` is the set of variables `v`
whose `P_{e,l,v}` is *not identically zero* for some literal of e.
This support is defined before choosing a numerical center T.

Clauses with support entirely on one side are local factors. Every
crossing clause depends on `L_boundary` and `R_boundary`,
the unions of its left and right support variables. Hence

```
F_T(x_L,x_R) = L_T(x_L) * C_T(x_L_boundary,x_R_boundary) * R_T(x_R).
```

Decompose the crossing factor by fixing assignments of the *smaller*
boundary side, using delta indicators on that side. This is a
constructive exact sum of at most

```
U(L,R) = 2**min(|L_boundary|, |R_boundary|)
```

separated products **over the entire polynomial ring Q[T]**.
Consequently, for every rational T, exact matrix unfolding rank over
Q is at most U(L,R). This is not a generic-rank estimate or an
empirical interpolation argument: it is an identity in Q[T] and remains
valid at all exceptional centers, including T=0.

Taylor expansion of the separated terms around a rational center
T=c gives products of polynomials in z. Modulo z**(q+1) the
factorization still has U terms **over the truncated polynomial
ring**. But the Q-matrix of one Taylor coefficient [z**j] has at
most (j+1)*U separated rank-one terms, since

```
[z**j] A(z)*B(z) = sum_{i=0}^j A_i * B_(j-i).
```

This is a coefficient **rank** upper bound, not a bound on
coefficient bit sizes, arithmetic work, or an efficient explicit
factorization. It is safe even if the polynomial support has
cancellations because the support is an over-approximation.

## Two distinct ordering problems

For a *specified* order, evaluating U at all n-1 prefix cuts requires
O(n*m) support-mask scans, after reading the polynomial coefficients.
For an identically-zero deformation, all nontrivial exact unfolding
ranks (and the n>=2 exact minimax bond rank) are zero; a symbolic
support upper bound can remain positive.
`uniform_support_profile` provides this cheap, exact certificate.

The research-only `minimax_uniform_support_order` computes

```
U_best = min_order max_prefix U(prefix)
```

using exact subset minimax DP with 2**n subset exploration and an
explicit capacity budget. This certifies an **upper bound** on the
best achievable exact TT bond dimension at every T. It is not the
actual minimax exact rank; the support bound can be loose, and
this implementation does not find an order in polynomial time.

Our other diagnostic, `minimax_unfolding_order`, enumerates truth
tables to find the **actual** best exact rank for small n, separately
at each T. Compare its result with U_best, but do not conflate
small samples with a growing-n theorem.

For an identity path of 64 variables, the natural order has support
bound 2 at every cut without enumerating 2**64 assignments.
For the legal identity-at-zero crossing pair witness, a grouped
order has support bound 2**k while an interleaved order has bound 2;
both bounds match measured exact rank at nonzero T. These statements
alone say nothing about the **specific spectral construction**.

## Test the actual finite spectral construction

`benchmarks.eth.spectral_rank_growth` uses
`construct_bounded_designs(formula, r=Q=R=2,
measurement_basis='projector')` for the *real* finite
spectral/measurement construction, on path, disjoint pairs,
XOR pairs and positive-OR clique CNFs.

For each admitted construction it records:

- source-pinned input family, clauses and original exact count;
- best uniform **polynomial-support** U and its variable order;
- exact rank profile on that order at certified centers for bounded n;
- exact *globally optimal* center-specific TT rank for smaller n;
- independent whole-deformation-polynomial sum checks where feasible;
- explicit construction refusals and unmeasured cases.

A construction refusal never becomes a zero-rank witness or a
successful counting result. The fixed r=Q=R=2 regime is **not**
the paper's parameter schedule. The certificate is about the exact
assignment deformation, not full recursive Sudoku generality.

This is a useful way to **refute a proposed structural invariant**:
if U_best grows sharply in actual families, then this particular
simple *support-based* guarantee cannot certify small ranks.
It does **not** follow that the *true* best rank also grows;
spectral cancellation could reduce it drastically. Conversely,
small measured exact ranks for finite n do not prove a uniform
bound or an efficient construction of an exact low-rank TT.

## Reproduction

```bash
python -m pytest -q tests/eth/test_support_rank.py -m checkpoint
python -m pytest -q tests/eth/test_support_rank.py -m integration
python -m pytest -q tests/eth/test_spectral_rank_growth.py
python -m benchmarks.eth.spectral_rank_growth \
  --families path matching xor_pairs clique --sizes 3 4 5 6 \
  --max-exact-n 6 --max-profile-n 6 \
  --output artifacts/eth-spectral-rank-growth.json
```

The opt-in growing-CNF workflow publishes raw evidence. This is
**not** part of per-commit latency-sensitive checkpoint testing.
