# Two-adic packet contraction: mathematical and formal proof map

**Status:** reconstruction of the October 25 appendix method plus an explicit Lean acceptance plan. This note is not an assertion that the full source recursion identity is currently proved in this repository or implemented in native Rust.

## The counting target

Encode bounded-degree #SAT as a tensor-network contraction over integers modulo \(2^{P_0}\), where \(P_0=n+1\) suffices to recover a count in \([0,2^n]\) exactly. Split the graph into packet groups, insert a Cauchy-style deformation, recover selected Taylor jets by interpolation, and expand each jet into weighted modes. Each mode becomes a product of **independent child contractions across groups**, but the internal coupling *within* a group must be preserved.

A schematic target theorem (notation intentionally abstracted from the actual source declarations) is
\[
\boxed{
F(t+2^{a+1}\zeta)
\equiv
\sum_{\beta:\,{\rm weight}(\beta)<p}
       \prod_g Z_{g,\beta}
\pmod {2^p}.
}
\]
Here \(F\) is the exact packet contraction at a node, \(t\) is the interpolation center, \(\zeta\) is the local displacement, \(a\) is the packet scale, \(\beta\) is a finitely supported tuple of mode exponents, and \(Z_{g,\beta}\) is the child contraction for group \(g\) with the \(\beta\)-selected coefficients. In the Lean theorem, these need *actual declared definitions*, not merely symbols that make the equation true by definition.

This statement suppresses source-specific normalizations and coefficient-selection maps. Restoring them is a proof obligation, not notation cleanup.

## Required algebraic hypotheses

1. **Coefficient ring.** Work in the specified finite quotient/coefficient algebra, with \(2^p=0\) and any required odd-unit inverses established constructively. Every division needs an explicit invertibility witness; a rational expression is not automatically legal modulo \(2^p\).
2. **Packet construction.** A valid packing/partition maps every original tensor edge and port to exactly the intended group and maintains source incidence, signs, copied wires, ordered labels, and bounds on group sizes.
3. **Forward differences and Cauchy kernel.** Derive the exact local tensor entry polynomial, its coefficient arrays and inverses; establish source-normalization and canonical lift laws at creation precision.
4. **Weighted expansion.** Prove that terms of weight at least \(p\) vanish by valuation, and that the retained finite mode expansion is precisely the coefficient of the original deformed tensor product.
5. **Many-group routing.** Prove the edge/port reassignment function \(hroute\) and that, **after a fixed mode tuple is selected**, the global sum bijects with a product of child group contractions. Do not assume independence for individual factors within a group.
6. **Hermite reconstruction.** Match the source interpolation centers, differentiation order, Taylor jets and recovery coefficients. Prove the final target residue from the actually retained precision.
7. **Resource inequalities.** Establish packet size, depth decrease, number of mode tuples, integer bit growth, peak storage and base-case cost under the *same parameters* as the theorem.

The older experimental Lean work reportedly established a finite weighted recursion identity with arbitrary groups under \(2^p=0\), but its source-facing version retained a local packet hypothesis \(hpacket\); \(hroute\), generated packet cutoff and source integration remained unfinished. Treat that as a research result to reproduce/import, not a theorem already accepted on this repository's main branch.

## Quantitative envelopes that dominate

For a network with \(s\) edges and \(\lambda=\lceil \log_2 s\rceil\), the recorded appendix schedule uses

\[
r=64,\quad \epsilon=2^{-17},\quad
u_0=\lfloor \epsilon\lambda\rfloor,\quad
L=2^a,\quad D_{\rm arr}=64^{2a},\quad
H=\left\lceil s/\lfloor\sqrt\lambda\rfloor\right\rceil.
\]

Packet admission includes inequalities of the form \(M\ge2D_{\rm arr}^2\Delta\), \(M\ge LD_{\rm arr}\), \(2L\le\Delta\). Interpolation at a node may require \(K=M(2L-1)+1\) values; a stated creation precision has form
\[
p_t=p+8hD_t+8M(a+1),\qquad
h=\lceil3M/u\rceil,\quad D_t=L/2^{v_2(t)}.
\]
The retained jet order is \(q_t=h\max(0,u-v_2(t))\). The source's sufficient parameter schedule can be inactive at anything resembling a practical input: e.g. \(s=10^6\) gives \(\lambda=20\), \(u_0=0\), and an impractical nominal direct leaf \(H=250000\). See the [quantitative study](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) for derivation and caveats. None of these are a proof that no tighter valid schedule can exist.

The mode tuple count is bounded in the analysis by a term of type \(\exp(O(\sqrt{Mp_t/D_t}))\); the work of individual packet entries may be \(\exp(O(L\log s))\). Those are **not polynomial overhead**. Calling a fast local Hermite solver cannot erase the count of nonzero modes, recursive child calls or packet coefficient work.

## One Lean theorem hierarchy (bottom-up)

| Theorem | Contract | Minimum distinguishing test |
| --- | --- | --- |
| `packet_entry_exact` | Source tensor entry equals finite coefficient expansion at its creation precision | Exhaustive tiny packet with negative signs, zero and mixed valuations |
| `mode_weight_cutoff` | Every omitted mode vanishes under the quotient assumption \(2^p=0\) | Boundary weight \(p-1\) retained, \(p\) discarded |
| `group_route_bijection` | Every valid assignment routes to a unique tuple of group-local assignments, preserving the tensor product | Two nonempty coupled groups with crossing ports |
| `mode_product_contraction` | Fixed-mode full contraction equals product of child contractions across groups | Within-group non-rank-one counterexample |
| `packet_recursive_identity` | The boxed formula follows from the previous results, with all source normalizations present | Exhaustive small ring quotient + mixed groups |
| `interpolation_recovery` | Reconstructed residue equals original \(F(0)\) modulo requested \(2^p\) | Coincident residue and unit/nonunit difference adversaries |
| `resource_bound` | Recursive work, bit growth and peak space satisfy asserted global bound | Symbolic recurrence proof plus instrumented witness traces |
| `rust_refinement` | Executed Rust path denotes the corresponding original Lean source program | Source-pinned independent Lean/Rust state and output traces |

One especially useful regression is to *mutate* the routing map or cutoff boundary in the test theorem and require the acceptance proof to fail. A genuine proof must expose these mistakes rather than absorb them into an overly strong hypothesis.

## Better implementations without changing the theorem

- Cache a certified irreducible polynomial for the required residue field, rather than a literal exponential candidate enumeration; retain the exact algebra and independently verify irreducibility.
- Use sparse, valuation-pruned packet coefficient extraction only when truncation is proved safe at every destination precision.
- Reuse interpolation products/weights, perhaps with standard exact polynomial libraries; count all necessary function evaluations, not just arithmetic around them.
- Consider direct *jet* evaluation to avoid unused coefficients only after a Lean proof that truncated operations commute with coefficient extraction and canonical lifting.
- Search improved finite parameter schedules subject to **all** packing, recursion shrinkage, unit separation, precision and complexity conditions; performance alone cannot authorize an altered theorem.

## Definition of completion

A green result consists of: the source-backed many-group recursion theorem checked in Lean with no `sorry`, no hidden packet/source axioms and no noncomputable runtime substitution; its measured Rust implementation on a real nonterminal counting path; and a separate proof of the full primitive-machine time/space envelope. Passing any one alone is useful but insufficient.
