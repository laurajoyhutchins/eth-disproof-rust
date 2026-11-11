# Execution and evidence

This page describes the **accepted `main` tree**, not pending PR branches. A
stage being constructible in Rust, having a fixture, or having a pinned source
hash is not the same thing as executing the original Lean code.

## Accepted execution boundaries

| Capability | Entry point / evidence | What is established | Not established |
| --- | --- | --- | --- |
| Bounded semantic #SAT oracle | `cargo run --bin lean-eth-reference`; Rust unit tests | Finite CNF parsing and small-instance counts via bounded enumeration | The source-defined Lean counting algorithm or its complexity bound |
| Source-defined native frontend | `cargo run --bin eth-frontend`; `docs/m2-runnable-frontend.md`; native frontend tests | Physical Rust `BitProgram` execution of the pinned `Native.frontendCommand` for supported inputs; preserves/checks specified ports | Any #SAT answer, independent Lean state parity, or full native counter |
| Selected native machine fragments | `src/native_*.rs`, `src/remaining.rs` and their tests | Source-correlated Rust instruction behavior and boundary/refusal tests | Composition into the entire original algorithm |
| Generated literal machine tables | Merged [code generation PR #150](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/150) | Deterministic Rust generation from 61 pinned original Lean literal program tables | Full closed `QueryStreamProgram` export, independent Lean runtime differential, or nonterminal counting |
| Source identity | `reference/source-manifest.json` | A catalogue of source Git revision and recorded blob IDs; tests validate local pin *format and coverage* | Independent byte-for-byte verification of those blobs or semantic equivalence |
| Original Lean execution | See draft [query exporter PR #145](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/145) | Progress on restoring pinned Lean/Mathlib belongs to that PR, not to an accepted `main` conformance gate | A completed original source query or a Lean/Rust differential run on `main` |
| Full machine differential | Draft [#154](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/154) and stacked hosted-Lean gate [#156](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/156) | Proposed full-state comparison and source-execution workflow | A successful original-Lean trace receipt and differential comparison accepted on `main` |
| Nonterminal source-native #SAT count | `src/remaining.rs`; [counting gate #100](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/100) | Unfinished stages must refuse, not substitute the bounded semantic oracle | One accepted end-to-end nonterminal count |
| Primitive TM2 refinement and complexity | [resource gate #110](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/110) | Outstanding mathematical obligations are explicitly identified | A TM2 step/tape bound or an ETH theorem established by Rust execution |

**Terms are not interchangeable:** Rust `BitProgram` instruction totals are
not the original primitive Turing-machine transition count. Live Rust stack
bits are not tape occupancy; wall time and allocations are implementation
measurements, not a proof of asymptotic bit complexity.

## Reproduce what currently runs

From `rust/lean_eth_reference` with Rust 1.99.1:

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings

# The native physical frontend. This does not count solutions.
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --quiet --locked --offline --bin eth-frontend

# Separate bounded, exponential correctness oracle. This counts solutions.
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --quiet --locked --offline --bin lean-eth-reference
```

The [Rust Actions workflow](../../../.github/workflows/rust.yml) runs on PRs,
pushes to `main` and manual dispatch. Check the workflow **for the exact
commit under discussion**; old local test totals and earlier green commits do
not validate later heads.

## Acceptance tests for the next milestones

1. **Independent Lean/Rust transition equivalence:** run the pinned original
   Lean implementation and Rust on identical legal and adversarial initial
   states. Compare program counters, *all* registers/stacks, emitted output,
   each transition, terminal/cleanup state and bounded refusal. Preserve the
   command, exact commits, toolchains and hashed trace artifacts.
2. **One complete nonterminal native count:** accept a CNF with a nontrivial
   source-defined count, traverse the real high-query/leaf/DFS path without a
   host enumeration fallback, and compare the complete result independently.
3. **Separate resource accounts:** profile implementation time/allocations
   alongside source-instruction steps, and separately justify the primitive
   TM2 transition/tape accounting needed for mathematical complexity claims.

Unknown, unsupported and unexecuted must remain visible as such. Research
branches and PR descriptions are proposals until their exact heads are
reviewed, tested and merged.
