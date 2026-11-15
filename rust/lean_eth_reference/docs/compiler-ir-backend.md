# Canonical compiler-IR Rust backend

**Status:** one production executable-IR emitter, an explicitly bounded Lean 4.34.1 subset. This does not establish G1 release acceptance or execute the original ETH counting program.

## Authority

The canonical executable Lean-to-Rust route is the in-process compiler in [`rust/native_lean_backend`](../../native_lean_backend/README.md). It receives borrowed `Lean.IR.Decl` objects from the pinned Lean 4.34.1 process and emits standalone Rust. The `eth-compiler` frontend calls its existing `scripts/compile-bundle.sh` publisher. There is **no second runtime or emitter** in the ETH CLI.

The earlier `leanfran 0.6.0` adapter from PR #184 is retained in Git history and acknowledged in [NOTICE](../../../NOTICE.md). It used Lean 4.35.0 and was never a verified production ETH compiler. The public `compiler-ir` route no longer invokes it; old leanfran-generated receipts are rejected by the native bundle validator.

## Current invocation

With the exact Lean 4.34.1 installation and Rust 1.99.1:

```sh
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1
(cd rust/native_lean_backend && lake build && bash scripts/check.sh)

cargo run --locked --offline -p lean-eth-reference --bin eth-compiler -- compile \
  --backend compiler-ir \
  --source-repo "$PWD" --source-revision "$(git rev-parse HEAD)" \
  --source-path rust/native_lean_backend/examples/PropertyDef.lean \
  --source-toolchain-path rust/native_lean_backend/lean-toolchain \
  --lake-root "$PWD/rust/native_lean_backend" \
  --module PropertyDef --root Property.hop \
  --output rust/native_lean_backend/artifacts/canonical-ir.rs \
  --receipt rust/native_lean_backend/artifacts/canonical-ir.receipt.json
```

The command currently accepts **one root and one source module per bundle**. Imported transitive declarations beyond the supported native closure are not certified. The native bundle script builds a standalone Rust library, validates that the requested root appears in the generated closure, and records hashes for the source, compiled Lean module, generated Rust and native backend. `eth-compiler` independently binds this bundle to the original Git-committed source and rejects a mismatched bundle, toolchain, root, digest, or status.

Reverify the artifact without executing Lean or running a backend:

```sh
cargo run --locked --offline -p lean-eth-reference --bin eth-compiler -- verify \
  --backend compiler-ir \
  --source-repo "$PWD" --source-revision "$(git rev-parse HEAD)" \
  --source-path rust/native_lean_backend/examples/PropertyDef.lean \
  --source-toolchain-path rust/native_lean_backend/lean-toolchain \
  --module PropertyDef --root Property.hop \
  --artifact rust/native_lean_backend/artifacts/canonical-ir.rs \
  --receipt rust/native_lean_backend/artifacts/canonical-ir.receipt.json
```

The embedded backend report permits the verifier to recheck the bundle without a second manually produced report file. A failed verification invalidates the receipt, not the original source.

## Other source path

A source definition without executable Lean IR may be represented as a shared core-expression DAG through the separate `--backend residual-expr` path. This **does not generate executable Rust**. Source-defined `StructuredCalls`/`BitProgram` lowering retains its existing specialized semantics and requires independent full-state agreement with original Lean execution.

Do not automatically route an unsupported executable-IR declaration to the symbolic producer. Both must be tied to the same original source, with missing computational dependencies refusing. No `leanfran` fallback, duplicate GMP/`Rc` runtime, Python compiler wrapper, or enumerative #SAT substitute is permitted.

## Remaining acceptance work

- Complete packaging for multiple roots and unchanged imported projects; this adapter currently uses the single-root native bundle.
- Verify transitive source provenance and computational relevance, not only Git identity for one source file.
- Add the typed, demand-driven residual consumer and exact physical `BitProgram` equivalence.
- Finish G1 acceptance on three substantial unchanged Lean programs and G2 on a complete nonterminal counting machine.
- Establish formal Lean-to-Rust semantic and TM2 resource correspondence. A successful native compile and finite differential tests are **not** proof certificates.

See [the source acceptance obligations](../../../research/lean-rust-acceptance.md) and [issue #193](https://github.com/laurajoyhutchins/eth-disproof-rust/issues/193).
