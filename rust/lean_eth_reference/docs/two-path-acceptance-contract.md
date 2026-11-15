# Two-path Lean codegen acceptance contract

**Status:** canonical native IR backend and a non-executable residual-expression producer, both fail closed. Neither certifies the full ETH counting algorithm.

## One user-facing compiler, distinct source semantics

The `eth-compiler` CLI has two explicit routes. `compile --backend compiler-ir` drives the existing **in-process Lean 4.34.1 compiler** in `rust/native_lean_backend`, using its already-supported atomic source/Rust bundle. It does not invoke leanfran. `compile --backend residual-expr` invokes the existing Lean core-expression DAG producer for a source definition that cannot be compiled from ordinary executable IR. The latter **does not emit Rust**.

There is no automatic substitution between routes, and no alternate production GMP/`Rc` runtime. Both share source Git identity, artifact digest, receipt format, strict refusal rules and `verify`. The physical `StructuredCalls`/`BitProgram` lowering remains specialized until its semantics have been independently matched to the original source.

## Commands

Build the pinned in-process compiler first and set `LEAN_PREFIX` to the pinned Lean 4.34.1 toolchain. See [the canonical compiler guide](compiler-ir-backend.md) for a reproducible `compile` and `verify` invocation.

For the symbolic route, with a Git-committed Lean module and matching source toolchain:

```sh
cargo run --locked --offline --bin eth-compiler -- compile \
  --backend residual-expr \
  --source-repo /work/lean-project \
  --source-revision "$(git -C /work/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --lake-root /work/lean-project \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --producer rust/lean_eth_reference/tools/lean-ir-smoke/ResidualGraph.lean \
  --output /tmp/lean-residual.json \
  --receipt /tmp/lean-residual.receipt.json
```

The `verify` command checks the Git source and artifact bytes. For native IR the original backend evidence is embedded in the receipt. A failure invalidates the receipt; it never authorizes executing a different algorithm.

## What the acceptance receipts establish

1. The original source file and toolchain pin bytes agree with Git HEAD and the requested commit.
2. Native IR artifacts must carry an actual pinned compiler-bundle receipt, the correct root and module, matching generated source hashes, a standalone Rust compile receipt, and explicit *not established* semantic and physical-refinement fields. Previous leanfran 4.35.0 reports are invalid.
3. The symbolic DAG must pass strict typed JSON/topological validation, bounded node counts, exact source-root identity, and non-executable output restrictions.
4. Successful output is staged and the receipt is published last. An old compile receipt is invalidated before a new attempt; generated code is never silently substituted on failure.
5. All receipts retain `executable_approved: false` until independent source equivalence is established. A generated and compiled Rust library is not an accepted ETH counting machine.

The compiled native bundle identifies one source file and its compiler closure. This does not independently establish the transitive Git identity or semantic equivalence of all imported declarations. The symbolic producer's `lean_defeq_checked` field is not itself an externally checkable kernel proof.

## Remaining work

A production G1 release requires broader unchanged Lean-project acceptance and proper closure/ownership semantics. G2 additionally requires justified source residualization, demand-driven delta/iota reduction, verified physical program composition, full original Lean/Rust state traces and resource correspondence. The original ETH-specific source graph machinery remains until those obligations are discharged.

See [the compiler guide](compiler-ir-backend.md), [residualization](core-expr-residualizer.md), and [source/refinement obligations](../../../research/lean-rust-acceptance.md).
