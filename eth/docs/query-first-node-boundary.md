# First QueryStream node: source-defined execution through pair preparation

Source: [`openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace)
Declarations: `QueryStreamProgram.command`, `nodes`, `nodeBody`, `PairNativeSetup.setupCaller`.

## Executable boundary

The single source-correlated Rust command `native_query_first_node::first_node_before_pairs_entry` executes:

1. `HighQueryAdapter.prepareHigh`, decoding the actual high-assignment word.
2. `QueryAssembler.Nodes.initializeNodes` and `QueryNodeFinish.guardCursor`.
3. When the source guard says there is a node, `QueryAssembler.Nodes.beginNode`.
4. `NativeLayoutLoad.command`, restoring all fourteen parked master words.
5. `SignatureHeadLoader.bootstrapNode`, through its actual 16×768 program lifted to 40×896.
6. `PairNativeSetup.setupCaller`, computing the physical free-coordinate counter and retained metadata.

This ends **before** `QueryStreamProgram.pairs`, the signed pair callback. It does not execute `QueryNodeFinish`, node iteration, or `QueryReconstruction.command`. The original command uses a while loop and later reads the fully reconstructed count from port 323; the bounded prefix executes at most the **first iteration** and no count is written to port 323.

The components are ordinary finite source-inspired BitProgram instructions using the existing single Rust instruction machine. There is no semantic #SAT oracle, provisional accumulator, generated signed-pair table, or runtime enumeration fallback.

## Reproduction and evidence

```sh
cargo test --locked --offline --test native_query_first_node_composition -- --nocapture
cargo fmt --all -- --check
cargo clippy --locked --offline --all-targets -- -D warnings
```

The integration test compares one compiled combined program against a *separate physical-stage replay* across all forty registers and 896 stacks for empty and one-node cases. It checks source guard behavior, preservation of parked words, free-coordinate/metadata ports, instruction limits and the continued explicit refusal of the full source `QueryStreamProgram.command` and `pairs` entrypoints. The test prints an exact-head source instruction and live-bit receipt. Both compared producers remain Rust. Independent unchanged-Lean differential evidence is not yet established.

## Separate blocked full-query graph export

An earlier [draft QueryStream AOT branch](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/191) successfully imported the original pinned QueryStream Lean module, but its graph exporter was killed on [workflow #43633617985](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/43633617985) when process-group RSS exceeded the configured 12 GiB envelope (observed 12,943,912,960 bytes). Ordinary Rust PR CI passing on that branch did **not** establish source graph or AOT success. Increasing the memory limit is not a substitute for demand-driven symbolic residualization with bounded term growth.

## Remaining

Implement the exact signed pair callback, tuple/visitor and commit stages, node readout and finish, reconstruction and the enclosing high/leaf/DFS/outer count. Then prove or independently check execution correspondence to pinned unchanged Lean, and separately account for numeric bit operations and live memory. Do not mark any full ETH resource or theorem acceptance on the basis of this finite first-node prefix.
