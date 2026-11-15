# Spectral decomposition of pair-swap operators

## Operator definition and eigenvalues

Take \(Q\) commuting involutions \(\Pi_1,\ldots,\Pi_Q\), each swapping a pair of coordinates. Define

\[
W=\frac12\sum_{i=1}^{Q}(I-\Pi_i),\qquad
V=\prod_{i=1}^{Q}\Pi_i,\qquad
M_0=Vf(W).
\]

On a joint eigenspace with \(j\) antisymmetric factors,

\[
W\mapsto j,\qquad V\mapsto(-1)^j,\qquad
M_0\mapsto(-1)^j f(j).
\]

So if \(f(j)=(-1)^j\) on a selected interval of Hamming weights, \(M_0\) acts as the identity there. Outside that interval, its spectrum depends on the chosen interpolation polynomial. This is exact linear algebra, subject to the polynomial degree and coefficient constraints.

The spectral identity does not establish that the operator preserves incidence constraints or permits recovery of the original count.

## Hamming-weight reduction

Commuting pair swaps give the binary Hamming-cube action. In a fully symmetric subspace, orbit sums depend only on Hamming weight, and the Krawtchouk transform diagonalizes the corresponding association-scheme operators.

A \(2^Q\)-coordinate calculation can then collapse to \(Q+1\) weight coordinates. But only if **both** the operator and the observations used to recover the count respect the symmetry.

Input incidence labels, copies and measurement rows usually need individual coordinates. Losing those distinctions may make the spectral calculation smaller while making the reconstruction invalid.

A replacement must preserve all four properties:

| Property | What to check |
| --- | --- |
| Support | The new operator obeys the source's incidence restrictions |
| Measurements | An integer measurement matrix exists and can be constructed efficiently |
| Arithmetic | Its rows, denominators, coefficients and 2-adic precision have controlled bit lengths |
| Recovery | The original #SAT count can be reconstructed without expanding the discarded exponential representation |

Rank reduction alone does not establish these properties.

## Higher-order group actions

Possible candidates include block permutations, signed-permutation actions, wreath products and rational sums of Galois-conjugate projectors.

For each candidate, calculate the actual orbit sizes, stabilizers, irreducible components and coefficient fields. Then apply it to **the original incidence system**, not a conveniently symmetric surrogate. A rational projector can reduce field extensions and still increase denominator height or violate support.

A negative control changes one incidence label. If one label destroys the symmetry used for compression, the supposed speedup should disappear, not be silently assumed.

## Rowspace and coefficient heights

The selector/Gram experiments found projected rowspace equivalences. But constructing a primitive rational row-reduced basis can increase integral row norms: one two-row example increased the maximum \(\ell_1\) norm from 3 to 4.

An independent subset of the **original integral selector rows** retains the source row-norm bound while spanning the same relevant space. That is useful, but still does not establish source-totality or the cost of generating every measurement witness. See historical [draft #95](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/95).

The related [exact tuple-streaming experiment](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/94) removed an unnecessary materialized Cartesian pool. It reduced iterator *storage*, not the number of mathematical tuples or the exact rational arithmetic needed.

## Counterexample: internal group factorization

A coupled group does not generally split into independent factors:

\[
A=\begin{pmatrix}
1&\tfrac12\\
\tfrac12&\tfrac38
\end{pmatrix},
\qquad \det A=\tfrac18\ne0.
\]

This matrix is not rank one. A product of one-variable marginals cannot reproduce its joint weights. The recursive construction may factor across routed **groups** after selecting modes. It does not generally factor *inside* a group.

Likewise, large treewidth does not certify hardness for this method. A grid has row-transfer algorithms with \(2^{O(\sqrt n)}\operatorname{poly}(n)\) cost. If a proposed solver struggles on a grid, compare it with that baseline before claiming structural difficulty.

## Comparison experiment

Use four paired families: fully symmetric, one broken orbit label, coupled bounded-density groups, and high-width incidence graphs.

Measure the same exact answer and:

- realized orbit/weight counts, support and measurement rows;
- \(\ell_1\) row norms, numerator/denominator bits and 2-adic precision;
- **all** operations and memory needed to construct and reconstruct the count;
- recursive calls and peak live coefficients.

Reject candidates that fail incidence or exact recovery, require an exponential basis expansion, or reduce local rank while increasing total work.

[Recursive contraction](two-adic-recursion.md) · [Full cost model](cost-model-and-benchmarks.md) · [Literature](literature.md)
