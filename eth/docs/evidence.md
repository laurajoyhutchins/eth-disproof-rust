# Executable coverage and verification evidence

This page distinguishes source-defined executable paths, generated artifacts, and the independent verification still required.

## Implemented execution paths

| Runs or exists on main | What that establishes |
| --- | --- |
| `eth-frontend` / `Native.frontendCommand` | Executes the pinned source-defined CNF frontend as a physical `BitProgram`; no satisfying-assignment count |
| `eth-terminal-count` | Handles supported terminal CNFs through the source frontend, classifier and an explicitly identified primitive count-port adapter; nonterminal formulas refuse |
| `lean-eth-reference` | Bounded **exponential** #SAT oracle; checks small exact counts but is not the proposed source counter |
| `src/native_*.rs` | Selected high, cache, signature, tuple, pair and terminal machine fragments; fragments do not imply the full query |
| Literal table codegen | Deterministic generation from selected pinned original Lean literal tables; not full `QueryStreamProgram` construction |
| `reference/source-manifest.json` | Recorded source Git revision and blob identity catalogue; source identity is not semantic equivalence |
| Trace comparison and profiling tools | Checks trace shapes and differences; a comparator passing its own fixtures is not an independent original-Lean execution |

Evidence is attached to its **exact commit**. The canonical stage registry lives in [`src/remaining/registry.rs`](../src/remaining/registry.rs). Historical merges [#150](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/150), [#154](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/154) and [#158](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/158) explain the original boundaries. Evidence from those merges does not establish behavior at a newer head without corresponding tests.

## Outstanding acceptance tests

**One original nonterminal count.** Run the source-defined query, high/leaf, DFS and outer composition on a nontrivial CNF. Do not invoke the host oracle when a source constructor is missing. [The remaining dependency map](remaining-lean-port.md) and [counting gate #100](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/100) describe the route.

**One independent machine differential.** Execute the pinned original Lean program and the Rust result on identical initial states. Compare PC, *all* registers and stacks, ports, transitions, output, halting and refusal. Historical [draft #156](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/156) worked toward the original-source gate; a cached fixture is not an independent producer.

**One primitive resource argument.** Rust instruction counts, occupied stack bits, wall time and allocations are **not** TM2 transitions or visited tape cells. The abstract identity under source-graph agreement proved in [#178](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/178) is useful but leaves the Rust source-refinement and full counting graph obligations. See [resource gate #110](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/110).

## Reproduce current checks

The workspace pins Rust 1.99.1.

```sh
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo clippy --locked --offline --all-targets -- -D warnings

# Source-defined physical frontend. Does not count.
printf 'p cnf 3 3\n1 0\n1 2 0\n-2 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin eth-frontend

# Supported terminal count: 2^3 for three variables and no clauses.
printf 'p cnf 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin eth-terminal-count

# Separate exponential oracle. Five solutions.
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | \
  cargo run --quiet --locked --offline -p lean-eth-reference --bin lean-eth-reference
```

The [Rust workflow](../../.github/workflows/rust.yml) reports the exact head checked. A green run from yesterday validates yesterday's commit, not today's.

[Compiler acceptance](../../research/lean-rust-acceptance.md) · [Independent differential specification](independent-differential-and-accounting.md)
