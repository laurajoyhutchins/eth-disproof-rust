# The recursive 2-adic identity

## The equation we need

The appendix turns a bounded-degree #SAT instance into a tensor contraction. For \(n\) Boolean variables, exact recovery of the count uses a residue modulo \(2^{n+1}\).

Packets are deformed, sampled at interpolation centers, expanded into weighted modes and routed to smaller group contractions. The central identity has the schematic form

\[
\boxed{
F(t+2^{a+1}\zeta)
\equiv
\sum_{\beta:\,\operatorname{weight}(\beta)<p}
\prod_g Z_{g,\beta}
\pmod {2^p}.
}
\]

The hard part is the equality between the *original tensor network* on the left and the routed child networks on the right.

- \(F\) is the packet contraction at the current node.
- \(t+2^{a+1}\zeta\) is the local deformation around an interpolation center.
- \(\beta\) selects a finite tuple of modes; its weighted degree determines which terms survive modulo \(2^p\).
- \(Z_{g,\beta}\) is the child contraction of group \(g\), with the selected mode coefficients.

This is notation for the theorem we want, not a claim that the schematic equation above is already the exact source declaration. Source-specific normalizations, tuple indexing and coefficient maps must appear in Lean.

## Why the cutoff works

A mode with valuation at least \(p\) vanishes in a coefficient algebra satisfying \(2^p=0\). Modes of weight \(p-1\) must survive; those of weight \(p\) must be discarded.

The proof has to say exactly how mode weight controls valuation. It cannot assume arbitrary rational division in a quotient ring. Odd denominators need explicit unit witnesses; nonunits cannot be inverted by analogy with a field.

The expansion is finite, but **finite is not synonymous with cheap**. The number of retained tuples and the bit length of their coefficients both matter.

## Where the groups become independent

Fix one mode tuple \(\beta\). The routing map must send every edge, port and copy label to the correct child network. Only after proving a bijection between the original assignments and the tuple of child assignments may we rearrange the sum into

\[
\text{contribution of mode }\beta
  = \prod_g Z_{g,\beta}.
\]

This is factorization **across** independent routed groups. It is not permission to separate coupled factors inside one group. The [non-rank-one matrix counterexample](spectral-group-actions.md#a-two-by-two-obstruction) is a small test of that distinction.

In earlier exploratory Lean work, a finite weighted identity with arbitrary groups was reported under \(2^p=0\). The source-facing theorem still relied on a packet hypothesis `hpacket`; a proved routing map `hroute`, generated packet cutoff and source correspondence were not established on this repository's `main`.

## The enormous parameters

Let \(s\) be the tensor-network edge count and \(\lambda=\lceil\log_2s\rceil\). The recorded sufficient schedule chooses

\[
r=64,\quad \epsilon=2^{-17},\quad
u_0=\lfloor \epsilon\lambda\rfloor,\quad
L=2^a,\quad D_{\rm arr}=64^{2a}.
\]

It requires packing inequalities including

\[
M\ge 2D_{\rm arr}^{\,2}\Delta,\qquad
M\ge LD_{\rm arr},\qquad
2L\le\Delta.
\]

For \(s=10^6\), \(\lambda=20\), so \(u_0=0\). The nominal leaf threshold is

\[
H=\left\lceil\frac{s}{\lfloor\sqrt\lambda\rfloor}\right\rceil
=250{,}000.
\]

A direct \(2^H\) leaf is not a practical computation. This is a limitation of the **stated sufficient schedule**, not a proof that no tighter admissible schedule exists.

At a node, one specified interpolation construction uses

\[
K=M(2L-1)+1,\qquad
p_t=p+8hD_t+8M(a+1),
\]
\[
h=\lceil3M/u\rceil,\quad
D_t=L/2^{v_2(t)},\quad
q_t=h\max(0,u-v_2(t)).
\]

A sharper local interpolation kernel does not eliminate its \(K\) recursive evaluations. The mode count has a bound of the form \(\exp(O(\sqrt{Mp_t/D_t}))\); implicit packet-entry expansion may cost \(\exp(O(L\log s))\). These terms are not polynomial overhead.

Derivations and qualifiers are in [the parameter study](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md).

## The Lean proof, in pieces

| Lemma | What it must establish |
| --- | --- |
| `packet_entry_exact` | The source packet entry equals its finite coefficient expansion at the creation precision |
| `mode_weight_cutoff` | Exactly the modes of weight at least \(p\) vanish |
| `group_route_bijection` | Every source assignment has one correctly labelled group-local decomposition |
| `mode_product_contraction` | Fixed-mode contraction factors across routed groups |
| `packet_recursive_identity` | The boxed equation, with original normalizations and coefficient maps |
| `interpolation_recovery` | Retained jets recover \(F(0)\) modulo the requested precision |
| `resource_bound` | Depth, child calls, coefficient bits and peak space satisfy the claimed bound |
| `rust_refinement` | Rust executes the same source-defined program, checked against independent Lean traces |

Test the exact boundaries, not just happy cases: weights \(p-1\) and \(p\), zeros and negative signs, nonunit interpolation differences, two coupled groups, and a deliberately corrupted route. A false route must make the theorem fail.

## Work that might pay

Certified irreducible-polynomial construction can remove the literal field-search overhead. Sparse coefficient extraction can avoid coefficients already known to vanish. Product-tree interpolation may reduce arithmetic around the evaluations. A direct-jet method could be more interesting, but it needs a proof that truncation commutes with the relevant source operations and lifts.

Any new packet schedule must satisfy all the original packing, shrinkage, precision and recovery hypotheses, or replace them with a new proof.

The end point is **one source-backed Lean recursion theorem**, one matching executable nonterminal count, and one primitive-machine resource argument. These are three separate tests.

[Compiler correspondence](lean-rust-acceptance.md) · [Cost and adversarial instances](cost-model-and-benchmarks.md)
