# Original Lean value semantics on one Rust runtime

The pinned Lean 4.34.1 compiler compiles **original Lean source** into in-process compiler IR, then generates standalone Rust. No JSON IR or alternative Lean parser is introduced.

## Canonical value representation

The compiler uses the mainline immutable, reference-counted `__LeanValue` representation for constructors, projections and first-class functions. Its arbitrary-precision `Nat` is powered by the **mainline GMP implementation**. Signed `Int` reuses the **same GMP integer storage and arithmetic**, not a separate BigNat algorithm. Valid UTF-8 strings, persistent arrays of boxed UInt64, and persistent lists of boxed UInt64 use additional variants of the same canonical `__LeanValueRepr` enum.

Generated binaries require system `libgmp` but **do not link or load the Lean runtime**. One compiler/backend/runtime object API is used, with no competing production Nat implementation. The separate `runtime-primitive-registry.tsv` contains seven non-Nat primitive adapters, while `is_nat_primitive` handles the three source Nat operations and other mainline GMP operations.

| Original Lean source functions | Implementation | Oracle comparisons |
| --- | --- | ---: |
| Nat.add, Nat.sub, Nat.mul | Mainline GMP integer operations with Nat subtraction saturation | 43 |
| Int.add | Signed integer addition using existing GMP storage | 10 |
| String.append, String.utf8ByteSize, String.length | Valid UTF-8 concatenation, byte and Unicode scalar counts | 33 |
| Array.push, Array.size | Persistent boxed UInt64 array and Nat length | 10 |
| List.reverse._redArg | Persistent boxed UInt64 list reversal | 5 |
| **Total** | **Ten original-source operations, seven new adapters** | **101** |

Original Lean definitions are inspected in `examples/Item30IRProbe.lean` and compiled through live in-process IR using `examples/Item30Conformance.lean`. Lean independently evaluates the same functions and creates **101 expected results**. Inputs include integers above 512 bits, signed values, underflow, empty/large collections, `UInt64::MAX`, non-BMP Unicode, combining marks, embedded NUL, quotes, backslashes and newlines. One Nat test uses transitive dependency-closure code generation, not merely one-function compilation. Strings are passed to the Rust test through literal UTF-8 byte arrays to avoid source escaping bugs.

## Reproduce

With pinned Lean 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`, Linux x86-64, Rust 1.99.1, C compiler and system GMP development files:

    cd rust/native_lean_backend
    export LEAN_PREFIX=/path/to/Lean-4.34.1
    lake build
    bash scripts/check.sh

The post-#221 combined mainline suite covers **16,344** scalar, join, multi-root, immutable-object, first-class function, GMP Nat, finite Float, enum and extended unsigned comparisons, plus the **separate 1,920** fixed-width primitive matrix. The new 101 original-source comparisons produce **16,445** core assertions and **18,365** with the separate primitive matrix, **subject to successful exact-head integrated CI**. Randomized property tests and independent upstream project probes are separate.

`check-item30.sh` independently compiles the generated Rust using `rustc` and Cargo in debug/release, with Lean runtime environment variables removed, executes identical inputs, enforces strict Clippy, and checks that the final executable does not link Lean. GMP uses intentional audited FFI unsafe code; forbidding all unsafe code in generated Rust would be incorrect.

## Boundaries and exclusions

The checked IR coverage ledger permits only **31 bounded constructor variants out of 48**. Erased arguments are accepted solely as type parameters for Array primitives, never as runtime values. All unsupported IR must produce structured refusal; negative cases cover unsupported Nat bitwise operations, String mutation and Array indexing, with previous output files preserved.

Dynamic Rust `__LeanValue` inputs are a trusted caller boundary: wrong enum variants may panic. The tests do **not** establish general memory-sharing, mutation, exceptions/IO, arbitrary Char APIs, generic collections, malformed UTF-8, unrestricted first-class functions, or the original noncomputable ETH counting program. Finite differential testing is not a semantic-preservation theorem. G1/G2 remain separate acceptance gates.


## Cross-call ownership: bounded transfer, not RC equivalence

For directly compiled function calls, the emitter now transfers an object
argument without cloning it **only** when all of these hold:

- The call is in a top-level, straight-line body with no lexical join.
- The object variable occurs exactly once in that call.
- The remaining IR tail contains no use or reference-bookkeeping operation
  involving the variable, and its unsupported control-flow forms conservatively
  prevent the transfer.

Otherwise the existing owned `Rc`-backed value is cloned, so aliases remain
valid. This eliminates one class of artificial transient Rust references at
known final uses, without introducing another runtime or accepting new IR tags.

`examples/CrossCallFixture.lean` holds the source-defined interprocedural
conformance cases. Its independently Lean-evaluated oracle produces 512
comparisons covering consumed values, retained originals, returned aliases,
and duplicated operands across noinline compiled functions. The integrated
gate runs debug, release, and strict Clippy checks.

**Not established:** physical reference-count correspondence with Lean.
The generated runtime uses `Rc::strong_count` for `is_shared`, while
Lean IR explicitly manages reference counts with `inc`, `dec`, and `del`.
Object lifetimes, unique-owner mutations, incoming/outgoing ownership, and
reference-count observations still need an exact operational simulation,
especially across branches, joins, closures, and calls. End-to-end output
equality on these fixtures is evidence for these executions, not a general
equivalence theorem or a G2 resource guarantee.

## Borrowed parameter observations

Lean 4.34.1 `Lean.IR.Param` carries a packed `borrow : Bool` field.
The canonical Lean C ABI shim now reads it from the source object and checks
the exact pinned representation. `examples/BorrowFlagFixture.lean`
constructs source-native owned and borrowed parameters and confirms that the
C accessor agrees with Lean's field values.

The emitter refuses `Expr.isShared` on a borrowed function or join parameter
because the caller, not the callee, owns its reference-count lifetime. The
current generated Rust signature does not yet represent that borrow contract.
It also refuses `isShared` on tagged immediates at runtime, rather than
observing the artificial `Rc` allocation used by the adapter.

This is an explicit **restriction**, not a completion of reference-count
equivalence. Owned values may still have mismatched physical traces where
generated clones and erased `inc`/`dec`/`del` interact. Future acceptance
must prove or refuse those patterns, with source-C execution evidence.

## Explicit Lean IR reference-count bookkeeping

The pinned source IR uses `FnBody.inc`, `FnBody.dec`, and
`FnBody.del` for physical Lean reference-count operations. The emitted
`Rc` implementation previously ignored those instructions while exposing
`Expr.isShared` through Rust `Rc::strong_count`. An `inc` or `dec`
can therefore change a source-observable result without any corresponding
Rust operation.

The compiler now refuses a later `isShared` when source `inc`,
`dec`, or `del` may have occurred **earlier on the same execution
path**, including a path through a join point. Cases are scanned separately, without assuming that distinct variable
IDs denote different allocations. The audit follows `jmp` into lexical
`jdecl` bodies, with the reference-count history at each jump. Merely
declaring a join does not execute it. Nonrecursive lexical join scopes
and a bounded traversal match the canonical emitter's supported CFG.

This ordering matters: optimized Lean constructor code may inspect
`isShared` and *then* increment a field reference as it creates a
replacement object. That later increment cannot change the value of
the earlier observation. Rejecting the whole declaration breaks
already-verified source mutation programs without improving their
reference-count correspondence.

`examples/ReferenceBookkeepingFixture.lean` constructs actual Lean
`IR.FnBody` terms. It tests seven negative cases (each bookkeeping
instruction, possible alias across distinct IDs, paired increments and
decrements, and a nested join) and seven positive emissions (bookkeeping with no `isShared`,
`isShared` without bookkeeping, a sharing check followed by an
increment, and the same ordering across a lexical join). These are
emitter-contract checks, not a source execution trace theorem.

The C-emitter source also bypasses `inc` and `dec` with
`persistent = true`. The native Lean 4.34.1 ABI shim now reads the packed
`check` and `persistent` flags from the actual `Lean.IR.FnBody`
constructor layout. The audit keeps earlier nonpersistent effects but does
not invent an RC effect for persistent no-ops. Three positive source-IR
fixtures and one mixed-effect refusal enforce the distinction. This does
not make arbitrary `isShared` calls semantically equivalent to Lean C.

**Still unverified:** reference-count effects flowing through other
called declarations, runtime alias identity across values and closures,
and physical uniqueness decisions in optimized mutation. This local
gate does not authorize accepting those general cases. A subsequent
interprocedural ownership analysis or a faithful logical RC model is needed
before broadening supported observations. The source-defined
`MutFixture.rotate` remains an important regression: its `isShared`
precedes the field increments in the shared branch, even though the
code includes nested join declarations. Its existing original-Lean
differential tests must continue to pass.
