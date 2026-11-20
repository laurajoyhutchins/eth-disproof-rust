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


## OpenAI October 25 Cauchy-packet identity at the source algebra boundary

[`IndependentOpenAIPacketPreservation.lean`](../eth/proofs/IndependentOpenAIPacketPreservation.lean)
formalizes the cancelled polynomial
\(W_{xy}(T)=\prod_{q\in S\setminus\{y-x\}}(T-q)/C'(0)\),
where \(S=\{-L,\ldots,L-1\}\). The proof establishes that \(W(0)\)
is the identity on every *real* edge, for any injective map from edges
to (packet, slot) with aligned row/column slots; padded slots contribute
no edge indices. It then proves, for arbitrary row/column tensor products
in any commutative coefficient ring admitting a homomorphism from the
rationals, that the paper's Boolean-selector deformation satisfies
\(F(0)=\sum_X A(X)B(X)\) exactly.

The source's construction of a balanced labeled packet packing is **not**
verified by this proof. The proof consumes its essential disjointness
and endpoint-alignment invariant as `ValidPacking.injective`. Neither the
Cauchy perturbation at nonzero \(t+2^{a+1}\zeta\), precision pruning, nor
the source-derived OpenAI-to-Anthropic factor-network adapter is covered.
The file is included in the independent Lean gate, and its typechecking
status must be read from CI rather than presumed.


## Constructed packing and shared Anthropic source value

[`IndependentSourcePackingBridge.lean`](../eth/proofs/IndependentSourcePackingBridge.lean)
proves two further finite-network results.

1. `packingFromEnumeration` takes an **explicit bijective enumeration**
   of the real edges and places rank `k` in packet `k / L`, slot `k % L`.
   Its injectivity proof is the division/remainder identity; no
   `ValidPacking` proof is handed to the theorem. The convenient
   `enumeratePacking` witness uses a chosen finite enumeration, whereas
   `packingFromEnumeration` is the executable constructor once that
   enumeration is supplied.
2. `twoSideNetwork` is a **concrete Anthropic `Groundwork.Network`**
   on two nodes, with unit node-state sets and shared pair-label alphabet
   `E → Bool`. Its two source factor tables are exactly `row` and
   `column`, so `twoSideNetwork_value` proves the unmodified original
   `Network.value` equals `∑ x, row x * column x`.
3. `constructed_packet_eq_source_network` combines these statements:
   the OpenAI cancelled-Cauchy deformation at zero equals the Anthropic
   network's exact integer value after embedding into rationals.

The independently pinned Lean 4.34.1 workflow passed these theorems
at [run 44016858931](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/44016858931).
The subsequent explicit-enumeration constructor update must likewise
pass its own CI before it is considered checked.

### These are not the original encoding-to-encoding correspondence

The constructed `twoSideNetwork` is *an exact, source-type-correct
encoding of the OpenAI network's value*. It is **not** asserted to equal
the specific network constructed by Anthropic's SAT algorithm.
Its single pair label is a complete Boolean edge assignment, with an
alphabet of size `2^|E|`. The canonical encoding can destroy sparsity
and cannot transfer either algorithm's complexity theorem.

Likewise, rank-based packet placement proves the edge alignment and
injectivity needed at `T=0`, **not** the appendix's color-orientation
properties, deterministic conditional-expectation labeling, upper
packet count in the prescribed color classes, or its per-symbol load
bound. Those must be established for the actual appendix procedure.

Finally, this direct source-value square is an equality over the
rationals after casting integer tensor entries. It does **not** by
itself establish the appendix's coefficient-extension, mod-2^p
nonzero-node deformations, or recursive mode bounds. The subsequent
proof should connect both *algorithm-generated* network constructors
to a topology-preserving common incidence factor graph, then
independently prove the packet balance properties.
