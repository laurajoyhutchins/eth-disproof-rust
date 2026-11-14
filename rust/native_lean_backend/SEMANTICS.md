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

The pre-existing combined suite covers 13,336 mainline scalar, join, multi-root, immutable object, first-class function and GMP Nat comparisons, plus a separate 1,920 fixed-width primitive matrix. The new 101 source-level comparisons bring these totals to **13,437** and **15,357** respectively, **subject to successful exact-head integrated CI**. Randomized property tests and independent upstream project probes are separate.

`check-item30.sh` independently compiles the generated Rust using `rustc` and Cargo in debug/release, with Lean runtime environment variables removed, executes identical inputs, enforces strict Clippy, and checks that the final executable does not link Lean. GMP uses intentional audited FFI unsafe code; forbidding all unsafe code in generated Rust would be incorrect.

## Boundaries and exclusions

The checked IR coverage ledger permits only **29 bounded constructor variants out of 48**. Erased arguments are accepted solely as type parameters for Array primitives, never as runtime values. All unsupported IR must produce structured refusal; negative cases cover unsupported Nat bitwise operations, String mutation and Array indexing, with previous output files preserved.

Dynamic Rust `__LeanValue` inputs are a trusted caller boundary: wrong enum variants may panic. The tests do **not** establish general memory-sharing, mutation, exceptions/IO, arbitrary Char APIs, generic collections, malformed UTF-8, unrestricted first-class functions, or the original noncomputable ETH counting program. Finite differential testing is not a semantic-preservation theorem. G1/G2 remain separate acceptance gates.
