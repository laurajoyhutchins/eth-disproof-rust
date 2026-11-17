# Two-path Lean codegen acceptance

**Status:** an executable-IR compiler route and a non-executable symbolic route, both fail closed. Neither certifies the original ETH counting program.

The user-facing `eth-compiler` has two explicit choices. `compile --backend compiler-ir` uses the **single native Lean 4.34.1 in-process compiler** in `compiler`, producing a complete standalone multi-root Cargo package. `compile --backend residual-expr` uses Lean to retain the shared expression DAG for a noncomputable source declaration that has no suitable compiler IR; that DAG is **not executable Rust**.

No automatic fallback from executable IR to symbolic, no leanfran production codegen, and no alternate GMP/`Rc` runtime are allowed. Both routes bind source Git file/toolchain identity, artifact hashes, typed receipt checks and refusal behavior. Source-specific `StructuredCalls`/`BitProgram` lowering remains specialized until independently verified.

## Native executable-IR route

See [the native compiler guide](compiler-ir-backend.md) for `compile` and `verify` commands. Repeated `--root` arguments produce one compiled Cargo package with a deduplicated transitive compiler-IR closure. The `--output` target must not exist; a successful atomic package contains `Cargo.toml`, `src/lib.rs`, and the native project `receipt.txt`. The external JSON `--receipt` includes the original native report and does not assert Lean/Rust semantic proof.

Verification checks the original source revision, toolchain, module and ordered roots; compiler identity; manifest and generated Rust digests; native receipt contents; and the explicit absence of semantic/physical verification claims. Tampering invalidates the external receipt. A previous leanfran adapter report refuses.

## Symbolic source route

For a Git-pinned Lean project and a compatible source module:

```sh
cargo run --locked --offline --bin eth-compiler -- compile \
  --backend residual-expr \
  --source-repo /work/lean-project \
  --source-revision "$(git -C /work/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --lake-root /work/lean-project \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --producer eth/tools/lean-ir-smoke/ResidualGraph.lean \
  --output /tmp/lean-residual.json \
  --receipt /tmp/lean-residual.receipt.json
```

The symbolic route uses a single source root, rejects opaque computational dependencies and produces a bounded, strictly decoded DAG, preserving the non-executable status. No hand-supplied JSON may be silently substituted as compiled Lean.

## Common trust boundary

The public receipt always has `executable_approved: false` and leaves `lean_rust_semantic_refinement` and `physical_bitprogram_refinement` at `not-established`. The native receipt also records `transitive_source_manifest=NOT_CAPTURED`. The Git blob establishes the original **file**, not proof that every reachable declaration came from it or that all imported definitions are computationally safe.

Outstanding: transitive computational dependency closure, a typed demand-driven residual consumer, source-identical physical instructions and state traces, complete original ETH counting composition, and primitive TM2 resource transfer.

See [core-expression residualization](core-expr-residualizer.md) and [Lean/Rust acceptance](../../research/lean-rust-acceptance.md).
