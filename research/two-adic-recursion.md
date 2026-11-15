# Two-adic packet contraction identity

## Proposed recursion equation

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

The proof must establish equality between the original tensor network on the left and the routed child networks on the right.

- \(F\) is the packet contraction at the current node.
- \(t+2^{a+1}\zeta\) is the local deformation around an interpolation center.
- \(\beta\) selects a finite tuple of modes; its weighted degree determines which terms survive modulo \(2^p\).
- \(Z_{g,\beta}\) is the child contraction of group \(g\), with the selected mode coefficients.

This is notation for the theorem we want, not a claim that the schematic equation above is already the exact source declaration. Source-specific normalizations, tuple indexing and coefficient maps must appear in Lean.

## Valuation cutoff

A mode with valuation at least \(p\) vanishes in a coefficient algebra satisfying \(2^p=0\). Modes of weight \(p-1\) must survive; those of weight \(p\) must be discarded.

The proof has to say exactly how mode weight controls valuation. It cannot assume arbitrary rational division in a quotient ring. Odd denominators need explicit unit witnesses; nonunits cannot be inverted by analogy with a field.

The expansion is finite. Its cost still depends on the number of retained tuples and the bit lengths of their coefficients.

## Group routing and factorization

Fix one mode tuple \(\beta\). The routing map must send every edge, port and copy label to the correct child network. Only after proving a bijection between the original assignments and the tuple of child assignments may we rearrange the sum into

\[
\text{contribution of mode }\beta
  = \prod_g Z_{g,\beta}.
\]

This is factorization **across** independent routed groups. It does not imply factorization of coupled factors within an individual group. The [non-rank-one matrix counterexample](spectral-group-actions.md#counterexample-internal-group-factorization) is a small test of that distinction.

In earlier exploratory Lean work, a finite weighted identity with arbitrary groups was reported under \(2^p=0\). The source-facing theorem still relied on a packet hypothesis `hpacket`; a proved routing map `hroute`, generated packet cutoff and source correspondence were not established on this repository's `main`.

## Parameter schedule and scale

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

A direct \(2^H\) leaf is not computationally practical at this scale. This is a limitation of the **stated sufficient schedule**, not a proof that no tighter admissible schedule exists.

### Exact obstruction to retuning the root alone

The fixed \(\varepsilon\) is not the only obstacle. For a root with \(M=s\),
the paper's \(\Delta=\lceil s^{9/10}\rceil\), and **any** positive
\(u_0\), the packing requirement forces
\(s\ge(2r^8)^{10}\). With \(r=64\) this is \(s\ge 2^{490}\).
Indeed, for every positive \(s\) representable in \(u128\) and every
\(r\ge3\), the first packing inequality is impossible under this
envelope, even if \(\varepsilon\) changes. A smaller *proved invariant
maximum degree* is a genuinely different assumption, not a free parameter.

See [the root-packing obstruction and exact hypothetical schedule checker](root-packing-feasibility.md).
No full recursion or new complexity bound is claimed.

### Packet-lemma floor independent of the degree envelope

Even with an ideal maximum-degree cap, the *existing* packet lemma
requires \(M\ge4LD_{\rm arr}^{2}\ge16r^8\) at a positive-width
root. Preserving the original strict \(M/8\) child bound forces
\(r\ge49\), giving
\(M\ge 531{,}726{,}889{,}113{,}616\) edges. At the paper's \(r=64\)
the floor is \(2^{52}\) edges. These are lower bounds on satisfying
the *lemma's sufficient hypotheses*, not on all possible counting
algorithms. See [the derivation](root-packing-feasibility.md).

### Executable necessary-condition preflight

For every positive edge count `s` representable in a Rust `u128`,
`lambda = ceil(log2 s) <= 128`. Thus `u_0 = floor(lambda / 131072) = 0`.
The stated active root condition `u_0 >= lambda^(4/5)` cannot hold.
More generally, it implies the necessary condition `lambda >= 2^85`,
before packing, precision and child-shrinkage constraints. It does not
prove that a different schedule cannot work.

The checked Rust audit reports this obstruction without constructing a field,
generating packets, enumerating `2^H` leaves or returning a #SAT count:

```sh
cargo run --locked -p lean-eth-reference --bin appendix-admission -- 1000000
```

This prints `lambda=20`, `root_u=0`, `extension_degree=80`,
`leaf_edge_exponent=250000` in a JSON refusal receipt, with exit code 2.
The input is a **tensor-network edge count**, not a variable count.
The leaf exponent is from the paper's *nominal threshold*, not measured work.

The preflight checks a **necessary** condition only. It must never be
interpreted as successful recursion, an independent Lean/Rust differential
or a comparison against brute force. A new finite-size schedule would need
the full packing/precision/shrinkage proof and one complete exact count
before any performance claim.

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

## Lean proof obligations

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

## Possible cost reductions

Certified irreducible-polynomial construction can remove the literal field-search overhead. Sparse coefficient extraction can avoid coefficients already known to vanish. Product-tree interpolation may reduce arithmetic around the evaluations. A direct-jet method could be more interesting, but it needs a proof that truncation commutes with the relevant source operations and lifts.

Any new packet schedule must satisfy all the original packing, shrinkage, precision and recovery hypotheses, or replace them with a new proof.

Completion requires a source-backed Lean recursion theorem, a matching executable nonterminal count, and a separate primitive-machine resource argument. These are three separate tests.

[Compiler correspondence](lean-rust-acceptance.md) · [Cost and adversarial instances](cost-model-and-benchmarks.md)
