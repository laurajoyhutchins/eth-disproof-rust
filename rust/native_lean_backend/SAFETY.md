# Native Lean compiler safety and conformance boundary

This document records what checklist #193 items 21–30 actually establish
for the opt-in native backend. Pinned host: Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52; Rust 1.99.1; Linux x86-64.

## Live ABI and ownership

Lean elaborates and compiles an IR.Decl. The same Lean process invokes the
Rust library with *borrowed* IR.Decl or Array IR.Decl objects and Strings.
The C accessors are compiled against that Lean installation's lean.h.

- C returns borrowed constructor fields and array elements; Rust never calls
  Lean decrement-reference-count or retains an IR pointer after returning.
- Rust copies declaration names, primitive signatures, generated text, and
  diagnostics into Rust-owned storage before returning.
- The Rust FFI function creates a new Lean-owned String with lean_mk_string.
- The ABI runtime probe allocates a constructor, verifies two tagged scalar
  fields, its constructor tag and arity, verifies a Lean String, and decrements
  its *own* allocations. Real Lean IR fixtures verify the currently accepted
  compiler constructor tags separately.
- This is not a complete source-by-source audit of *every* IR constructor
  and layout. The compiler is version pinned, not ABI-version portable.

The entrypoints catch ordinary Rust panics during code generation and
publication. They cannot recover from invalid pointers, OOM abort, hard
memory corruption, a mismatched library loaded by force, or process death.
Untrusted source must be compiled in a separately quota-constrained process.
Parallel Lean invocations and thread safety are not certified.

## Fail-closed structured diagnostics

A native failure is ERROR followed by a newline and a JSON object with
the stable keys status, declaration, construct, and reason. Errors detected
in Lean before the IR bridge also embed those fields as JSON in their
diagnostic. The construct field identifies a family (FnBody, Expr, IRType,
Primitive, Dependency, ResourceLimit, etc.); a reason includes the exact tag
or callee where the backend can recover it safely.

No refusal yields source output. A successful output path is a relative
.rs filename without traversal or symlink ancestors. The output is staged
with create-new in the destination's own directory, fully written and
file-synchronized, then atomically renamed. This preserves the old output
on refusal or write/rename failure; a **successful** compile may replace the
explicitly chosen regular .rs file.

Concurrent malicious directory renaming is outside this filesystem
threat model; there is no claim of race-free openat2 confinement or
directory fsync crash durability.

## Explicit resource caps

| Mechanism | Limit |
| --- | --- |
| Lean dependency discovery | 2,048 names |
| Rust dependency traversal | 2,048 declarations |
| IR body walk | 100,000 nodes per visited body |
| IR array | 1,000,000 elements per array |
| Name/control-flow depth | 128 |
| Generated Rust source | 4 MiB |
| Rust body generation/traversal | 10 seconds per body |
| Rust whole closure lowering | 15 seconds per closure |

Limits cover the Rust lowering stage, not arbitrary Lean elaboration or
process-wide RSS. The latter require OS isolation and remain open.

## Standalone Cargo acceptance

A source file produced by #native_rust_closure can be packaged without
rewriting its generated functions:

    bash scripts/package_crate.sh examples/generated_closure.rs native_pipeline artifacts/standalone_pipeline

The packager generates a minimal Cargo.toml and src/lib.rs without Lean
dependencies. It refuses to replace an existing Cargo project. The
acceptance script runs cargo test with LEAN_PREFIX, LEAN_PATH, and
LD_LIBRARY_PATH unset, including wraparound boundary assertions.

## What these tests do not establish

The pinned existing conformance fixtures compare 1,984 Lean-native and
Rust-generated scalar/Boolean/dependency/recursion results, plus negative
tests for Nat/String, sorry, unsupported extern/primitive dependencies, and
unsafe identifiers. This PR adds a same-process refusal/recovery test,
repeated host loading and unloading across CLI processes, publisher tests,
ABI probe, and standalone Cargo tests.

Outstanding tasks include a comprehensive version-derived IR constructor
matrix, isolated malformed object and fuzz inputs, process-wide resource
enforcement, three independent nontrivial Lean projects, and correctness
checks for large integers, Unicode, collections, memory-sharing semantics
and effects once those capabilities are actually supported. No formal
semantic-preservation theorem is claimed. Keep all unproved release boxes
unchecked until successful **exact-head** receipts exist.
