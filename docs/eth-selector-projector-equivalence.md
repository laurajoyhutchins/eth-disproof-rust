# Selector and projected exceptional measurement equivalence

## Statement

This establishes an algebraic identity for the **actual**
\`ImplicitAuxiliaryDesign\`, independently of finite resource limits
and the manuscript's numerical admission inequalities.

Let \(U\) be the matrix whose rows are the integer exceptional
tensor-product selector eigenvectors of the local-swap operator.
Distinct selector eigenvectors are orthogonal; the squared norm
of a product selector \(u_j\) is \(2^{t_j}\), where \(t_j\) counts its
off-diagonal local factors. The exact exceptional spectral projector is

\[
P = U^\mathsf{T} W U,\qquad
W=\operatorname{diag}(2^{-t_1},\ldots,2^{-t_c}).
\]

Every diagonal entry of \(W\) is **strictly positive**.

For one occupied incidence-label copy and one variable group, let
\(A\) map the group's variable coordinates to their occupied
auxiliary labels (with summed entries for repeated occurrences).
The original selector measurement matrix is \(B=UA\).
The new projected Gram matrix is

\[
G=A^\mathsf{T}PA=B^\mathsf{T}WB.
\]

For every \(x\in\mathbb Q^g\),

\[
x^\mathsf{T}Gx=(Bx)^\mathsf{T}W(Bx).
\]

Because \(W\) is positive definite, \(\ker G=\ker B\). Hence

\[
\boxed{\operatorname{rowspace}_\mathbb Q(G)
       =\operatorname{rowspace}_\mathbb Q(B).}
\]

This statement includes rank-deficient and zero-rank restrictions,
duplicate variable occurrences, and arbitrary finite group
coordinate selections. It does not require enumerating the
exceptional selectors, a dense \(D=r^{2Q}\) matrix, or any particular
numerical size schedule to *be true*.

The integerized fraction-free reduction in
\`eth/projected_gram.py\` returns an independent primitive integral
basis of \(\operatorname{rowspace}(G)\), so the source-level
measurement-space identity is preserved exactly.

## What is and is not invariant

For the same original CNF, variable/clause schedules, and implicit
auxiliary operator, the selector and projector transfers produce
the **same replacement polynomials, variable partition, clause
ownership and certified row-space directions**. Therefore every
cross-group target representable by one representation is also
representable by the other, at every spectral interpolation center.

The two concrete measurement matrices are **not identical**.
In particular, none of the following must agree:

- the number of measurement rows, hence \(\tau\);
- the primitive integer row \(L^1\)-norm ceiling \(D_{\mathrm{row}}\);
- the rational witness coefficients \(\lambda\) in that basis;
- the literal tuple-evaluation domain
  \((2D_{\mathrm{row}}+1)^{\#\mathrm{rows}}\).

This distinction matters because the manuscript requires
**quantitative** bounds on row count and row \(L^1\) magnitude,
not merely row-space existence. A projected basis often removes
dramatic selector redundancy, but its integer primitive coordinates
may be larger. A polynomial bit-height result does **not** by itself
establish the required numerical \(L^1\) bound.

The strict paper entrypoint now accepts the explicit opt-in

\`\`\`python
construct_paper_bounded_designs(formula, measurement_basis="projector")
\`\`\`

while keeping \`"selectors"\` as the default. Both options execute
the **same exact paper admission audit** and conditional-expectation
balancing schedule, then independently certify each actual
measurement matrix, \(\tau\), \(D_{\mathrm{row}}\), row-space
decomposition, label multiplicity, and the strict manuscript
row-count inequality. Neither substitutes toy parameters or a
Boolean-cube fallback.

The opt-in does **not** mean that the projected representation
is known to satisfy all numerical premises on **every** admitted
input. It can still refuse, and the global theorem acceptance
remains RED.

## Independently executed source evidence

\`reference/eth_measurement_basis_equivalence.py\` contains a
small-input independent spectral-sum oracle: it actually generates
all source selector rows, weights each selector by its exact
squared norm, and reconstructs \(P_{u,v}\).
The reference tests compare this to the real implicit
\`exceptional_projector_at(u,v)\` on diverse exact auxiliary
parameters and label pairs.

The transfer tests use both implementations with **the same
schedules and CNFs** and independently establish both inclusions
of each group's measurement row space using exact rational
linear-combination witnesses. They also compare constructed
replacement coefficients, per-center independent measurement
certification, separated Taylor coefficients, full Boolean-cube
deformation values, and exact final #SAT counts.

A concrete four-variable, three-center input demonstrates an
operational difference: the original selector-tuple evaluator
refuses on its measurement-tuple capacity, while the projected
representation completes the same exact center evaluation. The
independent fused exact evaluator computes the original selector
answer as well. Neither refusal nor shortcut constitutes an
asymptotic complexity result.

## Remaining construction obligations

The algebraic equivalence is universal; the executable source
comparisons are finite. Proving the **full** admitted construction
is total and bounded still requires:

1. a uniform row-count and integer \(L^1\)-norm certificate for the
   projected representation under the manuscript schedule, or a
   different compact representation preserving the required
   quantitative bound;
2. source-level bit-work and peak-storage bounds for the
   conditional-expectation balancing algorithm, every transfer
   polynomial, and all exact measurement witness solves;
3. elimination of fixed resource refusals through a correct
   explicit cost model, without claiming unbounded real machines;
4. connecting the resulting construction to the complete
   non-refusing recursive contraction and Sudoku parameter
   recurrence.

No one of these follows from the equality of row spaces.
