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

**A bounded generated heap mode now uses the physical Lean C adapter.**
`--cfg 'feature="lean-c-runtime"'` selects `generated_value.rs` for the
*unchanged* IR-emitted functions. `check-generated-heap.sh` compiles the
original `RuntimeHeapKernels.lean` source independently to Lean C and
the existing Reader to Rust, then compares source/runtime outputs and
physical reference counts. The admitted constructor
`RuntimeHeap.Pair.mk` has two tagged Nat fields. A generated function
projects a tagged field, and `observe` exercises the direct-call
closure. The test hashes the exact generated source and refuses
unsupported constructor layouts or bignum projection.

The nested `RuntimeHeap.Box.mk` fixture now transfers a heap child into
a parent without inventing an increment. The exact Reader-generated
`RuntimeHeap.payload` must retain a borrowed heap field before the
parent's last source-owned reference disappears. A shared-parent path
compares the original Lean C and emitted Rust C physical counts 1 → 2
and 2 → 1 and checks that the retained child survives. The unique-parent
path exercises the corresponding final-parent release. Both preserve
the original child allocation identity, validated independently on
300 additional pairs/stamps. Nested descendants currently contain
immediate fields; shell-only `del`, heap grandchildren and joins are
not yet established.

The wider compiler still does not use the C adapter by default. The
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


## Source `del`: verified runtime primitive, not yet emitted IR

The bounded Lean C adapter now calls the pinned `lean_del_object`
through `lr_exec_del` instead of substituting `lean_dec`.
`source_del` requires a unique owned `RuntimeHeap.Box.mk` shell
(physical RC 1), one live zero-credit borrowed `Pair` projection,
and the supported second tagged immediate. It transfers the Box
field's existing physical child credit into that projection without
`lean_inc` or `lean_dec`, then frees the shell only.

The differential probe executes explicit C and Rust **test-host**
shell deletion on source-generated `Box` objects. Both preserve the
same child identity, data, exclusivity and physical RC after releasing
the parent shell. Negative admission probes reject an unprojected
child and shared parent, without mutating source count.

This checks the execution-time primitive, **not** the complete
source-to-runtime `FnBody.del` theorem: the shell-deletion call in
this probe is test-host code, not actual Reader-emitted `del`.
A source IR declaration containing `FnBody.del`, joins, broader
constructor layouts and nested release cascades remain open.
