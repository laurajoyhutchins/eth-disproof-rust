# Compiler boundary

This directory owns the **single production executable-IR to Rust
backend** for Lean 4.34.1. The public `cli/` crate also owns the single
artifact-validation contract and standalone `lean-rust-compiler` binary.

Current concrete layout:

- `NativeRust.lean`, `lakefile.lean`, `lean-toolchain`: Lean-side
  compilation and public source commands.
- `frontend/ffi/abi.c`: **compile-time** borrowed compiler-IR accessors.
  This is not the planned execution-time Lean C adapter.
- `backend/src/lib.rs`, `backend/src/reader/`, `backend/src/names.rs`, `backend/src/primitives.rs`:
  one Rust emitter and its admission/refusal rules.
- `runtime/rust/immutable_value.rs`: currently embedded bounded GMP/`Rc`
  runtime. It is not a general source RC fidelity theorem.
- `fixtures/` and `examples/`: original Lean source and differential
  witness inputs. `scripts/`: pinned checks and project compiler.
- `docs/`: ownership/ABI design, coverage, source-C correspondence.

Do not add a parallel interpreter or Lean frontend. Preserve the source
`inc`, `dec`, `del`, borrow, move, reuse and release decisions.
The actual first Lean C execution-time handle adapter is
`runtime/lean-c/`, which owns allocation/retain/drop/borrow over
`lean_object *` and tests against original Lean/C. It is a bounded
physical FFI witness, **not yet** a replacement runtime for generated
Rust source.
The limited `RuntimeHeap.Pair.mk` constructor and projection path now
selects a physical Lean C execution runtime for the **same emitted Rust
functions** through `--cfg lean_c_runtime`. Only tagged Nat fields
are admitted, and this does not establish general source heap ownership.
The exact Reader-emitted `ScalarFixture.plus` is linked into a Lean
C-hosted executable in the same runtime gate, with original Lean output
comparisons. This first actual compiler emission is **scalar-only**:
the next gate is a generated heap-backed function using the Lean C
handle adapter for physical tracing. The subsequent
Rust-native runtime must implement the same interface.

See [architecture](docs/backend-first-architecture.md),
[runtime contract](docs/execution-runtime-contract.md) and
[status](docs/compiler-status.md).
