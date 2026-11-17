# Lean C execution-time runtime adapter

This is the first **real Lean C reference-count FFI slice**, built
against the pinned Lean 4.34.1 runtime using its public header. It is
not the compiler's borrowed IR-reader `frontend/ffi/abi.c`.

The Rust `Owned` and `Borrowed` wrappers in `src/lib.rs` carry a
real `lean_object *` and have distinct lifetimes. Construction consumes
owned fields. Retention invokes `lean_inc`. Rust `Drop` invokes
`lean_dec`. Borrowed fields do not acquire references, and a
`Borrowed<'_>` cannot outlive the owning handle via its safe API.
Physical reference counts and exclusivity are queried from the C
runtime itself, not from a Rust `Rc` approximation.

## Witness

`check.sh` compiles unchanged
`examples/OwnershipObjectTraceKernels.lean` with the **original Lean
C compiler**. A C observer calls the actual `create` definition,
while a Rust observer constructs an equivalent bounded constructor
through the C adapter. Both compare constructor tag/fields and
physical counts before and after an increment and decrement for
three inputs. A pinned Lean IO driver initializes the runtime.

```sh
LEAN_PREFIX=/path/to/lean4-v4.34.1 bash compiler/runtime/lean-c/check.sh
```

This witness establishes a working FFI execution boundary for
constructor allocation, owned transfer, borrowing, retain, release
and physical source count observation. It **does not** establish that
the compiler-emitted functions use this adapter. The next task is
making one emitted Rust function select the execution-runtime
interface, while preserving the canonical emitter and proving it
matches original Lean C. Persistent/multithreaded objects, closure
ownership and full G1/G2 coverage remain unsupported.

See [runtime contract](../../docs/execution-runtime-contract.md)
and [compiler status](../../docs/compiler-status.md).
