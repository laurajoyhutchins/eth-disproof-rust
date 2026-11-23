# Lean-native Rust code generation: bounded architecture experiment

Status: **experimental, not a replacement backend**. The branch introduces
`LeanNativeRustIR.lean` as a direct consumer of pinned `Lean.IR.Decl`. Until
the pinned branch CI completes, its generated program and refinement claims
remain **unverified**.

## Architecture reconstructed from current main

Lean 4.34.1 compiles original Lean declarations. The canonical backend
(`NativeRust.lean`, `backend/src/reader/`) passes a **borrowed live IR object**
through an exact-version Lean/C/Rust ABI, validates tag/field layouts, records
direct-call closures, and emits Rust against an admitted runtime contract.
This is *not JSON serialization*. The current Rust reader includes semantic
work as well as ABI machinery: expression dispatch, direct calls, use/ownership
analysis, constructors/projections, cases/joins, signatures and extern policy.
See [reader architecture](reader-architecture.md) and
[backend-first architecture](backend-first-architecture.md).

The Lean-native experiment reuses:
- `Lean.Compiler.compile` and `Lean.IR.findDecl`, including locally compiled
  and already imported executable compiler-IR declarations;
- the original Lean declarations as oracle programs;
- `rustc`/Cargo 1.99.1 for native execution;
- the existing Rust backend unchanged as a paired comparison.

It does **not** reuse or replace the Rust value/Lean-C runtimes because the
experiment admits only `UInt64`, `UInt8` Bool tags, scalar returns, direct
calls and exact two-constructor Bool cases. It emits wrapping arithmetic
using Rust's standard `u64`, with no custom runtime.

## Real IR admission boundary

`LeanNativeRustIR.lean` pattern-matches actual upstream `IR.Decl`,
`IR.FnBody` and `IR.Expr` constructors, not a reified copy. It constructs
an at-most-64-name executable closure by scanning native IR direct calls.
The emitter is total over its admitted cases and returns `Except String`
on unsupported expressions, externs, non-scalar types, erased runtime
arguments, refcount instructions, heap operations, join points, or missing
declarations. A failed closure produces **no output package**.

The generator's current `UInt64` whitelist is deliberately much smaller
than the canonical Rust backend's coverage. No source-level fallback or
definition substitution is allowed. Generated function identifiers encode
the UTF-8 name bytes injectively.

Upstream source (same pinned tag):
- [IR constructors and ownership operations](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/IR/Basic.lean)
- [IR environment lookup](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/IR/CompilerM.lean)
- [Impure LCNF → IR lowering](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Compiler/IR/ToIR.lean)

Crucial limitation: native access removes ABI tag decoding, **not** the
semantic burdens of checks for ownership, type/constructor layout, globals,
effects, calls, join scoping, closure conversion, runtime ABI, receipts or
external validity. Blind migration of `reader/` would discard useful
source-credit validation.

## Reproduction and comparison design

From a checkout with Lean 4.34.1, Rust 1.99.1, and the existing compiler's
Linux dependencies:

```sh
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1
bash compiler/scripts/check-lean-native-ir-probe.sh
```

The isolated test uses `examples/LeanNativeIRSource.lean` for both
emitters. Original Lean evaluates 49 edge pairs per function (zero, small
values, 32-bit maximum, 63-bit boundary, 64-bit maximum). Its oracle
generates 147 assertions per backend for `add`, a nested-call
`pipeline`, and `choose`. Rust is compiled/executed with Cargo; the
experiment also checks `cargo fmt --check`, strict Clippy, unsupported
`String` refusal twice and source-code hash determinism. One separate
branch gate permits arithmetic results to survive a branch-emission refusal.

The script writes a receipt with source/emitter/reader hashes, toolchains,
revision, total emitter lines, source size, elapsed wall time and peak RSS.
These measures include Lean startup and fixture execution; they are **not**
isolated emitter microbenchmarks and must not be interpreted as such.

| Measure | Existing FFI Rust backend | Lean-native experiment |
| --- | --- | --- |
| Input | Native `Lean.IR.Decl` via borrowed ABI | Native `Lean.IR.Decl` directly |
| ABI decoding | Required and version-pinned | Eliminated for local traversal |
| Semantic validation | Rich bounded ownership/call/constructor checks | Scalar-only, new smaller admission checker |
| Runtime | Existing Rust/Lean-C adapters for covered families | No runtime beyond Rust's primitive `u64` |
| Original-source coverage | Broader, proven only to bounded tests | To be measured |
| Kernel theorem about **emitted** Rust | Not established | Not established |
| Generated-code correctness / timing / RSS | Run paired fixture | Run paired fixture |

The existing [scalar operational refinement](../proofs/ScalarOperationalRefinement.lean)
includes an all-inputs model theorem for `UInt64` wrapping operations and
Bool branching. It does not prove the actual native or Rust emitters correct,
does not parse generated Rust, and does not establish `rustc` or physical
ownership correspondence. A future significant result would prove that
`generate` on a precisely admitted genuine IR grammar produces an
abstract Rust syntax with a simulation theorem, with separately validated
text emission and runtime behavior.

## Migration decision gate

**Default: retain the canonical backend.** This experiment is too small to
justify migration unless source-level tests are green at the exact branch
head *and* a later feature family shows meaningful removal of the C
borrowed-object decoder without rewriting its semantic checks.

An incremental hybrid would preserve existing Rust runtime, fixture,
publisher, ownership ledger, and provenance; Lean could eventually own
native IR admission and produce a checked typed emission plan. But such a
plan is only useful if its semantics are simpler to verify than the
present ABI, not if it recreates another independently maintained IR.

Do not claim full Lean compilation, runtime independence for heap values,
universal refinement, or completion of the noncomputable QueryStream G2 goal.
