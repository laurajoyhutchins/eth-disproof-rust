# Pair-swap spectra, incidence-compatible group actions and interpolation

**Status:** research program, with exact local algebra and counterexamples; **no** accepted replacement for the source counting algorithm.

## Canonical object and geometry

A model instance has \(Q\) commuting pair-swap involutions \(\Pi_1,\dots,\Pi_Q\) on an ambient coordinate space. Define
\[
W=\tfrac12\sum_{i=1}^{Q}(I-\Pi_i),\qquad V=\prod_{i=1}^{Q}\Pi_i,\qquad M_0=Vf(W).
\]
Each joint eigenspace is indexed by its number of antisymmetric swap factors, \(j\in\{0,\ldots,Q\}\). On that eigenspace, \(W\) has eigenvalue \(j\), and \(V\) has sign \((-1)^j\). Therefore \(M_0\) has scalar eigenvalue \((-1)^j f(j)\). Choosing \(f(j)=(-1)^j\) on a designated central interval gives *identity on that interval*, subject to the exact polynomial/degree and integer-coefficient constraints.

The symmetry is not free. The map must preserve the *incidence-compatible support* needed by the counting reduction, not only a pleasing spectrum. A group action that makes the operator low-rank but destroys the source support conditions is unusable.

## Why the Krawtchouk/Walsh basis is natural

The commuting involutions generate the binary Hamming-cube action. In a symmetric subspace, orbit sums are indexed by Hamming weight and diagonalized by a Krawtchouk transform. This can replace a dense \(2^Q\)-coordinate linear calculation with an \(O(Q)\)-coordinate weight calculation *when the input operator and all queried observables are actually class functions*. It cannot replace the original full problem when incidence labels, copies or requested measurements break that symmetry.

Questions to certify separately:

1. Does the candidate action commute with every source incidence constraint, rather than merely the ambient spectral operator?
2. Is the orbit/invariant subspace closed under tensor assembly, row selection and exact measurement reconstruction?
3. Can an integer measurement matrix be constructed in time subexponential in the original instance size, with controlled \(\ell_1\) row norms and coefficient bit lengths?
4. Can the count actually be recovered from the compressed measurements without re-expanding an exponential basis?
5. Does the complete source operation/bit-memory budget improve over the present method and a direct exact baseline?

These are conjunctive conditions, not a menu of optional desiderata.

## Higher-order actions and rationality

Potential generalizations include block permutations, signed permutation groups, wreath-product actions and central idempotents of a finite group algebra. The correct invariant is not just the rank of a central projector. For each candidate compute:

- Orbit and stabilizer sizes, conjugacy-class parameters and coefficient field of the irreducible projections.
- Degree and arithmetic height of the projector representation; exact common denominators and 2-adic valuations.
- Support after pulling the operator back to every input incidence and its copy/group structure.
- Number and bit height of the *measurements* required to identify the target count.
- Cost of constructing the representation, decomposing orbits, multiplying operators and applying the inverse reconstruction.

A rational/Galois orbit sum may reduce coefficient-field extensions but can enlarge integral denominators or destroy support. A non-rational character projector cannot simply be averaged and claimed equivalent without a proof that the resulting rational operator preserves the demanded measurement information.

## Selector/Gram evidence and its limit

For a weighted feature map with selector matrix \(U\), projected Gram products such as \(U^\mathsf{T}WU\) can have the same rowspace as the appropriately projected source selector system. In the historical [PR #95](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/95), an independent subbasis chosen from the *original integral selector rows* preserves the rowspace without increasing individual source row \(\ell_1\) bounds. Naive primitive RREF does not preserve that quantitative property: even a two-row example can increase maximum \(\ell_1\) from 3 to 4. This was a draft on the historical Python research branch, not a verified general reduction in current Rust main.

Rowspace equality by itself neither bounds witness generation nor proves that every valid original instance is representable. The source-totality gap and full coefficient/copy accounting remain open.

## Two traps found experimentally

**Do not split a coupled group.** The weight matrix
\[
A=\begin{pmatrix}1&1/2\\1/2&3/8\end{pmatrix}
\quad\text{has}\quad
\det A=1/8\neq0.
\]
It is not rank one. Multiplying independent component marginals inside a group changes the count. Valid whole-*group* factorization must be distinguished from invalid factorization *within* that group.

**Do not infer hardness from a minor.** An \(\Omega(\sqrt n)\) grid treewidth profile does not imply an exponential lower bound for the proposed method. For grids a row-transfer dynamic program may already run in \(2^{O(\sqrt n)}\operatorname{poly}(n)\). Use graph structure as a measured stress signal, never as a proof of a lower bound.

## A falsifiable replacement experiment

Take paired, source-preserving families: (a) high-symmetry inputs, (b) inputs with one broken orbit/copy label, (c) bounded-density coupled group cases, and (d) adversarial high-width instances. For each compare **exact count equality**, number of realized orbit weights, projector support size, measurement rows and \(\ell_1\), numerator/denominator bit heights, 2-adic precision, total exact arithmetic operations, peak bytes, and final recursive calls. Fail the candidate if an incidence identity breaks, denominators grow uncontrolled, a step enumerates a hidden exponential family, or no full count path is retained.

Research outcome sought: a source-correlated mathematical operator \(M\) with (1) certified support, (2) efficient integer construction and small measurements, (3) exact recovery, and (4) a proved **total** complexity benefit. Better rank alone is not enough.

Related notes: [recursion](two-adic-recursion.md), [complexity](cost-model-and-benchmarks.md), and [literature](literature.md).
