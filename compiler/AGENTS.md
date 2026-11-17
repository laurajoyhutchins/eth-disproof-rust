# Compiler boundary

This directory owns the **single production executable-IR to Rust
backend** for Lean 4.34.1.

Current concrete layout:

- `NativeRust.lean`, `lakefile.lean`, `lean-toolchain`: Lean-side
  compilation and public source commands.
- `native/abi.c`: **compile-time** borrowed compiler-IR accessors.
  This is not the planned execution-time Lean C adapter.
- `src/lib.rs`, `src/reader/`, `src/names.rs`, `src/primitives.rs`:
  one Rust emitter and its admission/refusal rules.
- `src/runtime/immutable_value.rs`: currently embedded bounded GMP/`Rc`
  runtime. It is not a general source RC fidelity theorem.
- `fixtures/` and `examples/`: original Lean source and differential
  witness inputs. `scripts/`: pinned checks and project compiler.
- `docs/`: ownership/ABI design, coverage, source-C correspondence.

Do not add a parallel interpreter or Lean frontend. Preserve the source
`inc`, `dec`, `del`, borrow, move, reuse and release decisions.
The next implementation gate is generated Rust calling the pinned
Lean C runtime for independent physical tracing. The subsequent
Rust-native runtime must implement the same interface.

See [architecture](docs/backend-first-architecture.md),
[runtime contract](docs/execution-runtime-contract.md) and
[status](docs/compiler-status.md).
