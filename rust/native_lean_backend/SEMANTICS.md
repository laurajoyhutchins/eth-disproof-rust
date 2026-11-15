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

Otherwise the generated code retains a nonowning compiler alias, which
preserves physical memory safety without introducing a Lean reference-count
increment. External `__LeanValue::clone()` now means a new owned source
reference; compiler-generated temporary aliases use `compiler_alias()`.
The distinction is explicit in the canonical runtime.

`examples/CrossCallFixture.lean` holds the source-defined interprocedural
conformance cases. Its independently Lean-evaluated oracle produces 512
comparisons covering consumed values, retained originals, returned aliases,
and duplicated operands across noinline compiled functions. The integrated
gate runs debug, release, and strict Clippy checks.

The original Rust `Rc::strong_count` observation is no longer authoritative
on this experimental branch. Each emitted value has an independent source
reference-count cell; emitted `inc`/`dec`/`del` update that cell. Rust `Rc`
remains responsible for storage safety. The runtime still requires a complete
ownership simulation across constructors, closures, imported primitives and
the public ABI before it can claim full correspondence. End-to-end output
equality is evidence for tested executions, not a general theorem or a G2
resource guarantee.

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

This remains an explicit **restriction**, not a complete reference-count
equivalence proof. The source-count ledger eliminates a known source of
artificial alias observations, but borrowed parameter transfer and external
object lifetimes remain separate acceptance obligations.

## Explicit Lean IR reference-count bookkeeping

Lean 4.34.1 uses `FnBody.inc`, `FnBody.dec` and `FnBody.del` to
manage ownership. The canonical Rust emitter now replays these instructions
against a logical source count, independent of transient Rust `Rc` handles.
The pinned Lean C ABI supplies the packed `checkRef` and `persistent`
flags for `inc`/`dec`; the emitter validates them instead of reading
nonexistent pointer fields. The supported increment delta is bounded
to 1,000,000, and, matching the pinned LLVM backend, decrement requires
delta 1.

`source_dec` releases owned constructor, array, list and closure children
when the logical count reaches zero; `source_del` releases only the
container shell, matching `lean_del_object`, and ignores tagged immediates.
An attempted source underflow or deletion of a nonunique heap object refuses
at runtime rather than being silently ignored. Borrowed array element reads
do not increment the count; owned reads do.

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
`IR.FnBody` terms. It tests six negative cases (each bookkeeping
instruction, possible alias across distinct IDs, paired increments and
decrements, and a nested join) and four positive emissions (bookkeeping with no `isShared`,
`isShared` without bookkeeping, a sharing check followed by an
increment, and the same ordering across a lexical join). These are
emitter-contract checks, not a source execution trace theorem.

**Still unverified:** universal correspondence of ownership transfer
across calls, closure environments, constructor mutation, and externally
supplied values; the pinned Lean runtime's multithreaded and sticky/
persistent reference-count states; and interactions between source count
and physical allocations after copy-on-write. The existing source-CFG
refusal remains in place for observations following earlier RC effects,
so this change is an executable foundation, not universal support.
The source-defined `MutFixture.rotate` remains an important differential
regression, including nested joins and unique/shared branches.

The source-count runtime is single-threaded: generated values use
`Rc<Cell<usize>>`, not a thread-safe Lean heap representation. The
supported G1 domain must remain explicit until the missing operations
have source-C differential evidence and a checked simulation relation.
