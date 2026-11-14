# ETH construction research notebook

**Coverage:** 31 October–14 November 2026. **Review snapshot:** 14 November 2026.  
**Canonical implementation:** [eth-disproof-rust](../README.md), source-pinned to [openai/math@4eaee87548250b2682affda7d05d947c05554bae](../rust/lean_eth_reference/reference/source-manifest.json).

This is a navigable record of mathematical investigations, failed shortcuts, implementation experiments and acceptance conditions. It does not certify the paper or claim that the Rust repository executes a general subexponential #SAT counter. All results marked *provisional* require independent reproduction; exact-head CI, Lean kernel checking and source correspondence are separate obligations.

## Read by question

| Question | Note |
| --- | --- |
| What changed during these two weeks? | [Chronology and decision ledger](2026-10-31-to-2026-11-14-ledger.md) |
| Can spectral compression, pair swaps or larger groups improve the algorithm? | [Spectral/group-action program](spectral-group-actions.md) |
| What is the recursive two-adic contraction identity, and what remains unproved? | [Two-adic recursion and Lean theorem map](two-adic-recursion.md) |
| What is actually compiled/executable from Lean, and where are G1/G2 blocked? | [Compiler and semantic-refinement map](lean-rust-acceptance.md) |
| Where are the huge parameters? Which experiments matter? | [Cost model and adversarial benchmarks](cost-model-and-benchmarks.md), plus the fuller [worst-case and polynomial-overhead study](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md) |
| Which previous papers and external results should we reuse? | [Annotated, linked literature](literature.md) |
| How do we use automated formalization safely on this research? | [LaTeX-to-Lean evaluation and theorem acceptance](formalization-evaluation.md) |

## Evidence vocabulary

- **Established in upstream Lean:** stated theorem/lemma covered by a pinned, actually checked Lean source. It does not automatically establish a stronger manuscript statement, the Rust implementation or practical cost.
- **Accepted on Rust main:** code and tests present in the exact main commit; only the claims in [execution evidence](../rust/lean_eth_reference/docs/evidence.md) apply.
- **PR evidence:** evidence and tests reported for a particular PR head; never conflate with main or with another stacked PR.
- **Prototype observation:** numerical/symbolic experiment on an explicitly bounded fixture; no asymptotic claim.
- **Hypothesis/open:** algebraic identity, cost improvement or execution correspondence still to be proved.
- **Refuted shortcut:** a route ruled out by explicit counterexample, complexity accounting or missing assumptions.

## Non-negotiable invariants

1. **Preserve the original construction.** Do not replace the source counting path with a host #SAT oracle, arbitrary enumeration or a fabricated finite table.
2. **Account for the whole pipeline.** Setup, preprocessing, packet expansion, live mode count, bit precision, recursive calls, memory, exact arithmetic and primitive-machine costs belong in every claimed improvement.
3. **Do not confuse the two mathematical routes.** The paper's global rational interpolation route and its sharper recursive two-adic tensor contraction are different constructions with different proof requirements.
4. **Work in Lean for claims about the theorem.** Executable Rust is an implementation target, not a proof assistant. Independent unchanged Lean source executions and kernel checks anchor formal claims.
5. **Fail closed.** Unavailable compiler IR, unsupported constructors, unresolved reductions, noncomputable data or exhausted resource limits must be visible refusals.
6. **Distinguish complexity statements.** The [upstream Lean scope note](https://github.com/openai/math/blob/main/lean/docs/378.md) describes a weaker bound than the October 25 manuscript's sharper announced claim. Do not silently transfer one bound to the other.

## Research-to-code workflow

A research candidate starts with an exact source definition and a claimed invariant, followed by either a Lean theorem or a counterexample. Only then should a Rust differential fixture be added. Record input family, source SHA, Lean and Rust toolchains, final count, instruction/bit-operation counters, peak live storage, refusals and all proof assumptions. A patch that only reduces isolated kernel time is recorded as a *local speedup*, not as an algorithmic improvement.

Existing entrypoints remain [the crate documentation index](../rust/lean_eth_reference/docs/README.md), [the stage registry](../rust/lean_eth_reference/src/remaining/registry.rs), and [the source/verification evidence matrix](../rust/lean_eth_reference/docs/evidence.md). This notebook deliberately avoids a parallel manually-maintained implementation-status registry.
