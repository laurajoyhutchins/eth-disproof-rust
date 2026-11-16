# Native Lean IR reader modules

The in-process Lean 4.34.1 compiler is one compiler, not a family of backends. Its C ABI accepts borrowed compiler IR objects, inspects them under a pinned constructor/tag contract, and emits a bounded Rust subset. This refactor moves implementation methods; it does not introduce serialization, ownership transfer of Lean IR, a second runtime, or a different source language.

## Source ownership

| Path | Responsibility |
| --- | --- |
| `src/lib.rs` | Lean C ABI entrypoints and panic/refusal boundary, canonical emitted runtime source, shared IR type contexts and unit tests |
| `src/reader/decode.rs` | Bounded reads and type/tag/constructor/name decoding from borrowed Lean objects |
| `src/reader/expr.rs` | Single checked expression-tag dispatcher; no independent parser |
| `src/reader/expr_call.rs` | Source-refined direct calls, PAP/AP closures, primitives, and ownership-aware lowering |
| `src/reader/expr_value.rs` | Source-validated constructors, projections, boxing, and sharing observations |
| `src/reader/usage.rs` | Conservative reference/use and last-use analysis for owned transfers |
| `src/reader/view.rs` | Checked, borrowed views of `FnBody` and `Alt` constructor fields; no owned/serialized IR |
| `src/reader/cases.rs` | Case alternatives, source-validated constructor families and scalar/object layouts |
| `src/reader/body.rs` | Scoped joins, IR bodies, branch control flow and variable environments |
| `src/reader/module.rs` | Dependency closure, root signatures, generated functions and multi-root output |
| `src/reader/mod.rs` | Private implementation facade; imports the one existing primitive policy and naming scheme |
| `src/primitives.rs` | Single source-validated primitive and runtime-external support policy |
| `src/names.rs` | Injective generated Rust identifier encoding |
| `src/runtime/immutable_value.rs` | Sole emitted GMP/Nat/Rc value representation; not a compiler IR data model |

The production `Reader::body` emitter now also consumes that same
borrowed `FnBodyView`. Source-tag layout and field offsets are decoded in
one place. Case layout verification and recursion remain in the original
case/body lowerers, preserving their mutually recursive grammar.

The borrowed control-flow view centralizes tag-to-field interpretation for dependency
discovery, ownership/use analysis, and source-CFG reference-count auditing.
Those traversals remain separate because lexical syntax, executable CFG paths
and conservative liveness are not interchangeable. The view exposes only
borrowed pointers from the pinned Lean ABI. It does not cache Lean objects,
silently widen supported IR, or replace the original emitter.

Reader stage methods are `pub(super)` within the reader module, except for the three FFI-facing emission methods and the bounded `Reader::string` decoder used when publishing source. Those four crate-visible methods are `pub(crate)`. Root and helper entrypoints remain unchanged; there is no user-facing Rust API expansion.

The source definition of a supported constructor, primitive or Lean IR tag remains authoritative. Source `sproj` is distinct from pointer-field `proj`. Unknown effects, missing declarations, unsupported constructor layouts, erased runtime operands and noncomputable source with unavailable IR must still fail closed.

## Verification

The first extraction was verified at commit `52fa5e8a544e278eb9fc9beff3dfb0e1da22dd93` through the native Lean compiler, generated Rust execution and Excession Git-source review. This second extraction must independently repeat the original Lean and generated Rust differential suite on **its own exact head**.

Run the native commands from `rust/native_lean_backend` after building the pinned Lean and GMP toolchain:

```sh
cargo fmt --all -- --check
cargo test --locked
lake build
bash scripts/check.sh
bash scripts/check-evidence.sh
bash scripts/check-imported-probes.sh
bash scripts/check-bundle.sh
bash scripts/check-native-runtime-parity.sh
bash scripts/compare-c-rust.sh
bash scripts/check-external-projects.sh
```

The pull-request workflows run these checks and preserve independent provenance. The Excession check additionally executes `agent locate`, `agent context` at the original and candidate revisions, and `agent verify`, leaving coverage gaps in the output. Excession's static dependency analysis is not a complete Rust call graph and its replay is not behavioral equivalence. Exact-head external Lean/Rust tests remain necessary.

This structural refactor does **not** establish the G2 source equivalence or resource bounds of the original noncomputable ETH counting program.

## Compared native receipts

The exact-head baseline `52fa5e8a544e278eb9fc9beff3dfb0e1da22dd93` and split-reader revision `924c96b8e19c11d3c556d3006f140d7b8ce0f1a3` independently passed all three PR workflows. We compared the two preserved `native-integrated-g1-evidence` ZIP artifacts directly:

- All **251 artifact paths** were present in both runs.
- All **24 matching `.rs` and `.c` files** were byte-identical.
- `native-compiler-bundle-receipt.txt` retained the same `generated_rust_sha256`: `c43f5f4dc112af456e53dc4b650f48f6e2b3649a377aa580470464d77c2b5dfa`.
- Both native smoke receipts reported **21,131 Lean differential assertions** and **23,051 core/matrix oracle cases**.
- The native backend/shared-library SHA-256 values changed, as expected from the refactored compiler source. Identity of the emitted Rust is an observed property of these checked inputs, not a universal equivalence proof.

The Excession output for the candidate retained `PARTIAL` source coverage, including `UNSUPPORTED_LANGUAGE` for Rust; its independent test/build obligations were not fabricated as completed receipts.

## Compilation and publication entrypoints

Both compilation modes use the same Lean.IR Reader and Rust runtime, and
share `scripts/lib/compilation-common.sh` for declaration/export-name
validation, destination checks and no-overwrite staged-directory publication.

- `compile-project.sh` builds an **unchanged Lake project** and publishes one
  multi-root Cargo library. This is the public `eth-compiler` route.
- `compile-bundle.sh` compiles a single **copied source fixture** and publishes
  a diagnostic bundle with the source, generated Rust, compiled rlib and hashes.
  It is a distinct evidence mode, not another backend or a replacement for
  unchanged-source admission.

The caller still chooses the source compilation, evidence fields and staging
directory. Common publication refuses existing outputs and dangling symlinks,
requires a complete staged receipt and checks that a no-overwrite move
actually succeeded. Its no-overwrite check is not a defense against a hostile
process concurrently manipulating the destination parent.

LCNF remains an optional read-only diagnostic of local Lean compiler state.
