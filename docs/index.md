# Count the assignments. Account for the work.

The problem is #SAT: given a Boolean formula, count its satisfying assignments exactly.

OpenAI's Lean development proposes a subexponential route. Here we take the construction apart: the algebra, the machine it defines, the Rust translation, and the cost of actually running it.

**A source-defined frontend runs. A general source-defined counter does not yet run on main.** Keep that distinction in view.

## The mathematics

The central object in the appendix is a tensor contraction evaluated through 2-adic interpolation and recursive groups. The identity we want to reproduce in Lean has the shape

\[
F(t+2^{a+1}\zeta)
\equiv
\sum_{\beta:\,\operatorname{weight}(\beta)<p}
\prod_g Z_{g,\beta}
\pmod{2^p}.
\]

The notation above suppresses packet and routing definitions. Those are precisely the hard parts, not details to wave away.

Read [the recursion](research/two-adic-recursion.md), [the pair-swap spectral construction](research/spectral-group-actions.md), or [the full cost analysis](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md).

## The machine

| We can execute | We still need |
| --- | --- |
| Source-pinned CNF frontend and selected machine fragments | Complete query → high/leaf → DFS → outer composition |
| Terminal-family counts and a separate bounded brute-force oracle | A general source-defined nonterminal count |
| Formal graph-to-machine identity under stated hypotheses | Independent original Lean/Rust full-state parity for the complete program and its resource bound |

The separate brute-force oracle is useful for checking an answer. It is **not** the algorithm being studied.

Follow [execution evidence](rust/lean_eth_reference/docs/evidence.md), [the missing stages](rust/lean_eth_reference/docs/remaining-lean-port.md), and [the Lean-to-Rust acceptance conditions](research/lean-rust-acceptance.md).

## The real cost

At \(s=10^6\) edges, one stated schedule gives \(u_0=0\). The nominal leaf size is \(H=250{,}000\). Calling the resulting direct sum \(2^H\) “polynomial overhead” would be absurd.

The question is not whether an individual interpolation or matrix operation can be made faster. It is whether the **entire exact count** becomes cheaper, including coefficients, bit lengths, children, memory and reconstruction.

Start with [the measured cost model](research/cost-model-and-benchmarks.md). The larger [parameter study](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) records the derivations.

## Research record

[What changed, October 31–November 14](research/2026-10-31-to-2026-11-14-ledger.md) · [Literature](research/literature.md) · [Formalization experiments](research/formalization-evaluation.md) · [Historical port notes](rust/lean_eth_reference/docs/README.md)

The [source manifest](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/reference/source-manifest.json) pins the original Lean tree. The [repository](https://github.com/laurajoyhutchins/eth-disproof-rust) holds code, tests and the underlying documentation.
