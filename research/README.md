# ETH research notes

*October 31–November 14, 2026. Notes on the pinned OpenAI ETH construction.*

## Recursive counting construction

The appendix is a recursive **2-adic tensor contraction**, not the body’s global rational-interpolation method with a faster matrix multiply. Packets, interpolated jets, weighted modes and independent *groups* must fit into one exact identity.

[Recursion identity](two-adic-recursion.md) · [Parameter analysis](../rust/lean_eth_reference/docs/worst-case-and-polynomial-overhead.md)

[Independent ETH formulations and comparison levels](independent-formulations.md) records the Anthropic reference encoding, bounded cross-model tests, and the mathematical/physical-machine boundary.

## Spectral compression and arithmetic

Pair swaps give a natural joint spectrum. Krawtchouk/Walsh methods compress symmetric coordinates. Neither observation is a counting algorithm until the source incidence, integer measurements, denominators and exact recovery survive the change of basis.

[Pair swaps and group actions](spectral-group-actions.md) · [Cost and adversarial inputs](cost-model-and-benchmarks.md)

## Executable correspondence

A program that produces the same answer on five tiny examples is not necessarily the Lean program. We need the actual declarations, the physical instruction graph, independent state traces and a resource argument. The distinction matters most for noncomputable source definitions and the finite fallback.

[Compiler acceptance](lean-rust-acceptance.md) · [What main actually executes](../rust/lean_eth_reference/docs/evidence.md)

## Observations and counterexamples

- **A complete bipartite OR formula has a closed-form count but may require an exponential intermediate table under dense elimination.** Exact elimination is not a complexity result.
- **A large grid minor is not a hardness proof.** Grid row-transfer dynamic programming already gives a subexponential baseline.
- **Low rank does not imply preservation of incidence constraints or exact count recovery.** Source support and integer measurement costs are part of correctness.
- **Modes in different groups can factor after routing; factors inside one coupled group generally cannot.**
- **Paper-admissible parameters may never activate at realistic sizes.** Record that rather than invent a substitute schedule.

The [dated ledger](2026-10-31-to-2026-11-14-ledger.md) gives the experiments and associated PRs. [Peer-reviewed references](literature.md) and the [LaTeX-to-Lean benchmark](formalization-evaluation.md) are indexed separately.

## Evidence categories

**Proved:** a theorem checked in pinned Lean with its hypotheses exposed.  
**Executed:** the identified original-source behavior ran, with reproducible evidence.  
**Measured:** an explicitly identified implementation and input family were profiled.  
**Proposed:** a change of representation, parameters or schedule still needs proof.

One result does not imply the others. In particular, lower rank does not imply lower total work, and a passing Rust test does not imply original Lean equivalence.

Keep all source identities, exact toolchains, counterexamples, arithmetic bit costs and known refusals alongside the claim. The [implementation registry](../rust/lean_eth_reference/src/remaining/registry.rs) tracks runnable stages; these notes do not replace it.
