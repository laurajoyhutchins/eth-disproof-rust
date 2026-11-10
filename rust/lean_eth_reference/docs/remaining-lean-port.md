# Remaining OpenAI Lean ETH executable path (v0.8.0 scaffold)

Source pin: [openai/math@4eaee87548250b2682affda7d05d947c05554bae](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT). This is a **structural port scaffold**, not a theorem translation or end-to-end counting implementation.

The new `src/remaining.rs` records the **executable dependency spine** in topological order, with Lean source paths, symbols, machine dimensions, and one of five states: `Executable` (Rust-exercised prefix), `Partial`, `Stub`, `Noncomputable`, and `ProofObligation`. It does **not** claim to enumerate every auxiliary theorem file in the much larger Lean development.

## Next executable work

The actual `QueryStreamProgram.nodeBody` is `beginNode` -> `NativeLayoutLoad.command` -> `SignatureHeadLoader.bootstrapProgram` -> `PairNativeSetup.setupCaller` -> `DifferencePairsProgram.command` (with `QueryExecution.PairStart`, `SignatureTupleComplete.command`, `QueryAssembler.commitPair`) -> `QueryNodeFinish.command`. The first, second and pair *setup* portions are executable Rust. In particular, `PairNativeSetup.expandCaller`, signed pair iteration, signature tuple DFS, node coefficient append and canonical count reconstruction are **not** implemented.

`QueryStreamProgram.command` feeds `HighQueryProgram.marked/accepted` via real high-assignment enumeration. Those, in turn, feed `NativeLeafRun.command` (preparation, marked greedy rounds, separate accepted query). `NativeLeafProgram.localCommand k` is a **40x896** bit machine. `NativeLeafProgram.command k` lifts it into the **80x1220** outer machine via terminal dispatch and leaf-bank load/export. `Native.outerCommand` connects frontend setup, disjoint counting DFS and positivity. `Native.entryCommand` selects between the bounded fallback and this large-input path; `Native.countingProgram` compiles it. `BitProgram.tm` and `GuardedCompiler.primitive` are separate finite TM2 refinement obligations.

## Invariants and stubbing policy

Every exported unfinished constructor returns `Err(Error::NotImplemented(source_symbol))` for every input, including zero-width cases. There is no fake `Halt`, `Skip`, zero count, bypass, unbounded count oracle, or accepted-query replacement. Machine dimensions appear in return types. Existing executable stages are left unchanged; their Rust tests **do not** establish Lean-source differential refinement. A genuine Lean import/trace comparison remains outstanding.

The `FiniteFallback` program has a *noncomputably selected* table in Lean. Constructing a finite lookup from exhaustive bounded data would be a distinct implementation that needs its own explicit table-generation and source-semantics checks. Until then it fails closed. The final theorem `SqrtLogSpace/Final.lean:exact_count_and_sat` is catalogued as a proof obligation, not represented as a Rust function that returns true.

Useful commands (when the verified Rust toolchain is restored):

```sh
cargo fmt --check
cargo test --offline
cargo clippy --offline --all-targets -- -D warnings
```

The scaffold adds three integration tests for graph ordering and failure-closed behavior. It does not use GitHub Actions minutes or claim a compilation/run that has not occurred.
