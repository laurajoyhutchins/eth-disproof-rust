# Lean-native Rust code generation: bounded architecture experiment

Status: **experimental, not a replacement backend**. The branch introduces
`LeanNativeRustIR.lean` as a direct consumer of pinned `Lean.IR.Decl`.
The paired source-oracle experiment **passed** in
[bounded run 45217007708](https://github.com/laurajoyhutchins/eth-disproof-rust/actions/runs/45217007708).
That run checked out a synthetic GitHub PR-merge commit
`ac71f586f5829b6e7394755e2e6d53e09b62fdba`; follow-up CI now checks out
the exact PR head before producing receipts. **No universal refinement of
emitted Rust is established.**

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
calls, nonrecursive scalar joins and exact two-constructor Bool cases. It emits wrapping arithmetic
using Rust's standard `u64`, with no custom runtime.

## Real IR admission boundary

`LeanNativeRustIR.lean` pattern-matches actual upstream `IR.Decl`,
`IR.FnBody` and `IR.Expr` constructors, not a reified copy. It constructs
an at-most-64-name executable closure by scanning native IR direct calls.
The emitter is total over its admitted cases and returns `Except String`
on unsupported expressions, externs, non-scalar types, erased runtime
arguments, refcount instructions, heap operations, recursive or borrowed
join points, or missing declarations. A failed closure produces **no output package**.

Source-inspected subtlety: the pinned compiler's source `Bool` pattern
uses `UInt8` as the `FnBody.case` type name, but still uses
`Bool.false`/`Bool.true` as the constructor identities with indices 0/1.
The first experimental admission rule wrongly expected type name `Bool`
and refused; the canonical `backend/src/reader/cases.rs` already
distinguished these representations. The corrected emitter checks both
the storage type and constructor identity, and explicitly rejects
invalid Boolean tags in the emitted Rust.

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
| Original-source coverage | Broader; same 147 comparisons pass | 147 bounded scalar comparisons pass |
| Kernel theorem about **emitted** Rust | Not established | Local actual IR arithmetic-rule check; no whole-program theorem |
| Generated-code correctness / timing / RSS | See measured paired results below | See measured paired results below |

The existing [scalar operational refinement](../proofs/ScalarOperationalRefinement.lean)
includes an all-inputs model theorem for `UInt64` wrapping operations and
Bool branching. It does not prove the actual native or Rust emitters correct,
does not parse generated Rust, and does not establish `rustc` or physical
ownership correspondence. A future significant result would prove that
`generate` on a precisely admitted genuine IR grammar produces an
abstract Rust syntax with a simulation theorem, with separately validated
text emission and runtime behavior.

## Bounded paired results

Run `45217007708` executed the original Lean functions on 49 fixed
boundary-value pairs, generating source-computed expected results. The
Lean-native Rust implementation passed 98 arithmetic/nested-call assertions
and 49 conditional assertions. The canonical FFI/Rust backend passed the
same 147 original-source comparisons. Each emitted library passed offline
Cargo tests, `cargo fmt --check` and strict Clippy. A previously unsupported
String-source declaration produced identical deterministic structured refusal
on both attempts, without an output package. Repeated native source
generation preserved its SHA-256 after identical formatting.

| Measured item | Lean-native | Existing FFI/Rust |
| --- | ---: | ---: |
| Original-source differential comparisons | 147 passed | 147 passed |
| End-to-end Lean emission process time | 0.83 seconds | 0.81 seconds |
| End-to-end process peak memory | 1,623,736 KB | 1,624,348 KB |
| Generated source bytes | 748 (two arithmetic roots) | 1,576 (all three roots) |

**The emitted-byte figures are not normalized to identical package
structure.** Scalar coverage is much smaller than the existing Reader,
and no code-generation-only benchmark exists. The tiny timing and memory
differences reflect mostly common Lean compiler initialization and should
not guide migration.

Source SHA-256: `aecf9766a24db0621adce75f66b38f9594aa47725f7a8d4336a674265ecf525a`.
Pinned compiler: Lean 4.34.1 (`5045d005`) and Rust 1.99.1
(`58cf8f9c3`). The base prototype had 239 lines (including comments);
the subsequently added local emitter rule theorem increases this count.

The branch now also checks `arithmeticIRRulesSound`, a *local theorem
about two genuine compiler-IR `Expr.fap` instruction shapes*: they render
the prescribed Rust wrapping operation text, and that operation has the
same modulo-`2^64` result as `UInt64` addition/multiplication for all
inputs. This is not an emitted-program semantics theorem; its exact-head
kernel and axiom audit status is recorded by the latest targeted CI run.

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
