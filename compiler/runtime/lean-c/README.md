# Lean C execution-time runtime adapter

This is a **real Lean C/Rust execution boundary**, built against
pinned Lean 4.34.1. It is distinct from the compile-time borrowed IR
accessors in `compiler/frontend/ffi/abi.c`.

The Rust `Owned` and `Borrowed` handles in `src/lib.rs` contain real
Lean `lean_object *` references. Constructor fields transfer owned
references. Retention invokes `lean_inc`, Rust `Drop` invokes
`lean_dec`, and borrowing is limited by the lifetime of its owner.
Physical count and exclusivity observations come from Lean C rather
than `Rc::strong_count`.

## Two independent execution checks

The integrated compiler conformance script
`compiler/scripts/check.sh` tests both:

1. **Heap ownership boundary:** the original
   `OwnershipObjectTrace.create` program is compiled to C. A Rust
   observer calls the pinned C runtime to construct the equivalent
   bounded constructor, then compares field representation,
   exclusivity and physical refcounts before and after a retain and
   release over three inputs.
2. **Actual emitted Rust in the Lean C process:** after
   `ReaderRustStatement.lean` captures and checks the real IR
   emitter's exact `ScalarFixture.plus` source, the script links those
   **unchanged generated Rust bytes** into the original Lean C
   executable. Its Lean IO driver calls the Rust entrypoint for 100
   pairs of UInt64 boundary values and compares against the original
   `ScalarFixture.plus` Lean function executed in that same process.

The generated code is not a separately typed or handwritten Rust
replacement. The wrapper only adapts the exported scalar C ABI.
Keep the exact emitted-file digest in the CI receipt.

## Still open

**Generated heap-backed Rust does not yet use the C adapter.** The
scalar proof validates the ABI and basic execution against Lean C,
while a different bounded handle test validates actual physical
ownership. Combining both as if they proved all constructor,
borrowed-projection, call/join and destructor semantics would be
incorrect.

The next acceptance target is one *compiler-emitted* heap constructor
and projection executed with these Lean C handles, followed by
ownership-sensitive call/join and nested release. Persistent and
multithreaded reference counts, arbitrary externs and all original
ETH G2 obligations remain unproved.

See [runtime contract](../../docs/execution-runtime-contract.md)
and [status](../../docs/compiler-status.md).
