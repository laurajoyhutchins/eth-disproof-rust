# Research questions

*October 31–November 14, 2026. Notes on the pinned OpenAI ETH construction.*

Three questions drive this work.

## 1. What is the algorithm actually doing?

The appendix is a recursive **2-adic tensor contraction**, not the body’s global rational-interpolation method with a faster matrix multiply. Packets, interpolated jets, weighted modes and independent *groups* must fit into one exact identity.

[Work through the recursion](two-adic-recursion.md) · [Read the source parameter study](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md)

## 2. Can we make the mathematics smaller?

Pair swaps give a natural joint spectrum. Krawtchouk/Walsh methods compress symmetric coordinates. Neither observation is a counting algorithm until the source incidence, integer measurements, denominators and exact recovery survive the change of basis.

[Pair swaps and group actions](spectral-group-actions.md) · [Cost and adversarial inputs](cost-model-and-benchmarks.md)

## 3. Can we run the original program?

A program that produces the same answer on five tiny examples is not necessarily the Lean program. We need the actual declarations, the physical instruction graph, independent state traces and a resource argument. The distinction matters most for noncomputable source definitions and the finite fallback.

[Compiler acceptance](lean-rust-acceptance.md) · [What main actually executes](../rust/lean_eth_reference/docs/evidence.md)

## Findings worth keeping

- **A complete bipartite OR formula can have an easy count but an exponential intermediate table.** Exact elimination is not a complexity result.
- **A large grid minor is not a hardness proof.** Grid row-transfer dynamic programming already gives a subexponential baseline.
- **A low-rank projector can still be the wrong projector.** Source support and integer measurement costs are part of correctness.
- **Modes in different groups can factor after routing; factors inside one coupled group generally cannot.**
- **Paper-admissible parameters may never activate at realistic sizes.** Record that rather than invent a substitute schedule.

The [dated ledger](2026-10-31-to-2026-11-14-ledger.md) gives the experiments and associated PRs. [Peer-reviewed references](literature.md) and the [LaTeX-to-Lean benchmark](formalization-evaluation.md) are indexed separately.

## What counts as a result?

**Proved:** a theorem checked in pinned Lean with its hypotheses exposed.  
**Executed:** the identified original-source behavior ran, with reproducible evidence.  
**Measured:** an explicitly identified implementation and input family were profiled.  
**Proposed:** a change of representation, parameters or schedule still needs proof.

One result does not imply the others. In particular, lower rank does not imply lower total work, and a passing Rust test does not imply original Lean equivalence.

Keep all source identities, exact toolchains, counterexamples, arithmetic bit costs and known refusals alongside the claim. The [implementation registry](../rust/lean_eth_reference/src/remaining/registry.rs) tracks runnable stages; these notes do not replace it.
