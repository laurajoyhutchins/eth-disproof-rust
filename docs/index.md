# ETH construction research

**Mathematics · Source refinement · Rust implementation**

Independent, source-pinned study of OpenAI's Lean ETH construction. The full nonterminal Rust counter and claimed resource bounds are **not** established here.

<div class="home-links" markdown="1">

[Research notebook](research/README.md){ .home-link } 
[Execution evidence](rust/lean_eth_reference/docs/evidence.md){ .home-link } 
[Two-adic recursion](research/two-adic-recursion.md){ .home-link } 
[Compiler acceptance](research/lean-rust-acceptance.md){ .home-link }

</div>

## Current boundaries

| Accepted work | Open obligations |
| --- | --- |
| Source-pinned frontend and selected machine fragments | One complete source-defined nonterminal count |
| Bounded exact correctness oracle, explicitly exponential | Original Lean/Rust full-state correspondence |
| Lean source and abstract-machine refinement components | Complete ETH declaration residualization and primitive resource theorem |

The [research ledger](research/2026-10-31-to-2026-11-14-ledger.md) documents the last two weeks of mathematical and compiler work. [The full-pipeline cost study](rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) identifies pathological parameters and hidden arithmetic overhead.

## Reading paths

**For the mathematics:** [spectral group actions](research/spectral-group-actions.md) → [two-adic recursion](research/two-adic-recursion.md) → [complexity benchmarks](research/cost-model-and-benchmarks.md) → [literature](research/literature.md).

**For the implementation:** [source/runtime evidence](rust/lean_eth_reference/docs/evidence.md) → [missing execution dependencies](rust/lean_eth_reference/docs/remaining-lean-port.md) → [G1/G2 compiler acceptance](research/lean-rust-acceptance.md) → [native backend semantics](rust/native_lean_backend/SEMANTICS.md).

**For historical experiments:** [the documentation inventory](rust/lean_eth_reference/docs/README.md) and [reconstructed Git history](rust/lean_eth_reference/docs/reading-the-history.md).

The repository's [source manifest](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/rust/lean_eth_reference/reference/source-manifest.json) pins the upstream Lean checkout. GitHub PR evidence is deliberately kept distinct from accepted source execution.
