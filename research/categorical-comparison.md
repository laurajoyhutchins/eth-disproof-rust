# Finite-matrix semantics for the ETH network comparison

The two algorithms are *not* identified term by term. Instead, their network
constructions must be evaluated into the same scalar semantics before any
comparison of modes, packets, or resource bounds.

## The categorical core

For a commutative semiring \(R\), a finite \(R\)-weighted kernel
\(f : A \to B \to R\) represents a network with input boundary \(A\) and
output boundary \(B\). Sequential composition contracts matching boundaries,
and parallel composition forms the Kronecker product:

\[
(g\circ f)(a,c)=\sum_{b\in B} f(a,b)g(b,c), \quad
(f\otimes h)((a,x),(b,y))=f(a,b)h(x,y).
\]

[\`IndependentCategoricalContraction.lean\`](../eth/proofs/IndependentCategoricalContraction.lean)
spells out and proves, using finite sums rather than a black-box category
axiom, the following laws:

1. Associativity and identities for network contraction.
2. Interchange for tensor products of independent networks.
3. The swap symmetry on entries and cyclicity of network trace.
4. Additivity and multiplicativity of closed-network values.
5. Functoriality and tensor preservation under a semiring homomorphism,
   including naturality of trace and finite weighted sums.

These are concrete *string-diagram laws* for finite weighted kernels. This
module does not package a complete Mathlib \`MonoidalCategory\` instance and
does not assert all Mac Lane coherence axioms via named associators/unitors.

For \(\rho_p : \mathbb Z \to \mathbb Z/2^p\mathbb Z\), the same identities
prove \(\rho_p(\operatorname{tr}f)=
\operatorname{tr}(\rho_p f)\). Thus taking a finite contraction and reducing
its exact integer output is the same as reducing every factor first.

## Actual source-backed squares

[\`IndependentCategoricalSourceSquare.lean\`](../eth/proofs/IndependentCategoricalSourceSquare.lean)
imports the already checked, pinned original-source proofs:

- \`IndependentETH.numSat_eq_count\` proves OpenAI/Anthropic finite CNF
  semantic equality for every list CNF, including unused variables and
  duplicates. Mapping the exact count to \(\mathbb Z/2^p\mathbb Z\) commutes.
- \`Groundwork.Network.value_merge\` proves that the *original Anthropic*
  network color-group merge preserves exact integral contraction; mapping
  that source theorem to \(\mathbb Z/2^p\mathbb Z\) commutes.
- \`IndependentETH.SourceNetwork.anthropic_merge_preserves_contraction\`
  connects Anthropic's source network to the common finite factor-sum
  contraction and the same coefficient reduction.

All imports are from the pinned upstream snapshots. The CI workflow rejects
unresolved admissions and runs Lean with the pinned Mathlib environment.

## Crucial absent source bridge

The general equality
\[
\rho_p\bigl(\operatorname{ev}_{\mathbb Z}(E_A(\varphi))\bigr)
 \stackrel{?}{=}
 \operatorname{ev}_{\mathbb Z/2^p\mathbb Z}
     (E_O(\tau\varphi))
\]
is **not** proved here. The original OpenAI October 25 appendix's two-adic
packet encoding is not connected to the shared factor network by a
source-derived normalization and incidence-preserving map. Neither its
nonzero deformation, weighted-mode cutoff, recursive group routing nor its
interpolation recovery can be supplied by abstract functoriality alone.

The earlier signed-swap factor has odd entries (e.g. \(-1\)).
Singlet Hamming weight is not itself a 2-adic valuation certificate. A
source-specific divisibility argument is mandatory before dropping terms.

The count-definition square and the Anthropic merge square genuinely
commute; the unproved network-encoding square remains an explicit open
research question. None of this asserts an ETH disproof, improved complexity
bound, or executable Lean-to-Rust correspondence.
