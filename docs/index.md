# OpenAI ETH construction: mathematics and implementation

This repository studies the mathematical construction and executable programs in OpenAI's Lean development for exact #SAT counting. It covers the two-adic contraction, the source-defined machine, the Rust implementation, and its resource bounds.

The source-defined frontend and selected machine fragments run. A general nonterminal counter and its primitive-machine complexity bound are not yet established on `main`.

## Two-adic tensor contraction

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

## Executable coverage

| We can execute | We still need |
| --- | --- |
| Source-pinned CNF frontend and selected machine fragments | Complete query → high/leaf → DFS → outer composition |
| Terminal-family counts and a separate bounded brute-force oracle | A general source-defined nonterminal count |
| Formal graph-to-machine identity under stated hypotheses | Independent original Lean/Rust full-state parity for the complete program and its resource bound |

The separate brute-force oracle is useful for checking an answer. It is **not** the algorithm being studied.

Follow [execution evidence](rust/lean_eth_reference/docs/evidence.md), [the missing stages](rust/lean_eth_reference/docs/remaining-lean-port.md), and [the Lean-to-Rust acceptance conditions](research/lean-rust-acceptance.md).

## Lean compiler IR to Rust

The general compiler (G1) uses Lean's own frontend and ownership-explicit compiler IR. There is one production Rust emitter, currently limited to a documented executable subset. The current standalone Rust value runtime is **not** a demonstrated substitute for Lean's entire runtime.

The implementation order is: prove the backend against Lean C execution, define and test the ownership/FFI contract, then replace runtime operations in Rust. Compiling the noncomputable original ETH machine (G2) remains a separate issue, and an independent proof kernel is not part of the compiler.

[Architecture](rust/native_lean_backend/docs/backend-first-architecture.md) · [Current status](rust/native_lean_backend/docs/compiler-status.md) · [Execution runtime contract](rust/native_lean_backend/docs/execution-runtime-contract.md) · [Build and use](rust/lean_eth_reference/docs/compiler-ir-backend.md)

## Complexity and implementation costs

At \(s=10^6\) edges, one stated schedule gives \(u_0=0\). The nominal leaf size is \(H=250{,}000\). The resulting direct sum requires \(2^H\) assignments. This is not practical at the stated scale.

A performance comparison must include the **entire exact count**: coefficient construction, bit lengths, child contractions, memory, and reconstruction.

Start with [the measured cost model](research/cost-model-and-benchmarks.md). The larger [parameter study](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) records the derivations.

## Research notes

[What changed, October 31–November 14](research/2026-10-31-to-2026-11-14-ledger.md) · [Literature](research/literature.md) · [Formalization experiments](research/formalization-evaluation.md) · [Historical port notes](rust/lean_eth_reference/docs/README.md)

The [source manifest](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/reference/source-manifest.json) pins the original Lean tree. The [repository](https://github.com/laurajoyhutchins/eth-disproof-rust) holds code, tests and the underlying documentation.
