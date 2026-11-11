# Rust ETH port documentation

This index separates **accepted contracts on `main`** from historical port
notes. Only source code and exact-head execution evidence determine which
operations are currently implemented; a historical chapter is not an
acceptance certificate.

## Current execution and verification contracts

| Document | Purpose |
| --- | --- |
| [Evidence matrix](evidence.md) | Supported execution, actual tests, pending independent Lean parity and TM2 obligations |
| [Remaining source path](remaining-lean-port.md) | Dependency spine, unsupported constructors and ordered native counting obligations |
| [Runnable frontend](m2-runnable-frontend.md) | Native `BitProgram` frontend ABI, CLI and output boundaries |
| [Compiled query table](compiled-query-table.md) | Strict source-pinned query table importer; importing is not proof of independent source generation |
| [Independent differential and accounting](independent-differential-and-accounting.md) | Harness contracts and reporting for actual original Lean execution |
| [Finite fallback disposition](m2-finite-fallback-decision.md) | Why source noncomputability must not be replaced by a hidden oracle |
| [Reading history](reading-the-history.md) | Constructed first-parent study sequence and original provenance |

The live stage catalogue is
[`src/remaining/registry.rs`](../src/remaining/registry.rs), not an
independently maintained status table in this documentation.

## Historical implementation notes

These documents preserve the rationale for successive ports, fixtures and
machine boundaries. They may describe a version, PR or missing piece that has
since changed. Consult the evidence matrix and current Rust tests before
relying on any status statement in them.

**Early machine and source-frame development:**
[integer cache v0.10](integer-cache-port-v0.10.md),
[H-cache v0.11](h-cache-iteration-v0.11.0.md),
[integer cache v0.12](integer-cache-v0.12.0.md),
[bootstrap v0.13](bootstrap-v0.13.0.md),
[signature loader v0.14](native-signature-loader-frames-v0.14.0.md),
[pair expansion v0.15](pair-expansion-v0.15.0.md),
[difference pairs v0.16](difference-pairs-v0.16.0.md),
[head support](head-support-port.md).

**Query and pair exploration:**
[signed pair preparation](m1-signed-pair-preparation.md),
[physical pair sign](m1-physical-pair-sign.md),
[Lean table codegen experiment](lean-table-codegen-experiment.md).

**Frontend and normalization progress:**
[frontend boundaries](m2-frontend-boundaries.md),
[outer I/O boundaries](m2-outer-io-boundaries.md),
[literal cleanup](m2-normalization-literal-cleanup.md),
[tautology source](m2-tautology-source.md),
[full source normalization](m2-full-source-normalization.md),
[terminal classifier](m2-terminal-classifier-source.md),
[terminal count](m2-terminal-count-source.md).

**Test history:** [TDD accuracy audit](tdd-accuracy-audit.md), which records
known test limitations and should not be interpreted as a current independent
Lean conformance receipt.

Source Git identity is pinned in
[`reference/source-manifest.json`](../reference/source-manifest.json).
The Rust and original Lean source trees have separate correctness and resource
accounting obligations.
