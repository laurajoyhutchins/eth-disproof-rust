# Item 30: Lean → standalone Rust semantic conformance

This document defines the exact tested subset of compiler checklist #193, item 30. It does not assert general Lean runtime support or a semantic-preservation theorem.

## Actual source and compiler

`examples/Item30IRProbe.lean` compiles original Lean definitions through the pinned Lean 4.34.1 compiler to inspect their real IR. The production Rust backend receives the same IR in-process without serialization. It emits standalone Rust, and it consults `runtime-primitive-registry.tsv` to recognize exactly ten source-native runtime calls.

| Original Lean IR operations | Implemented semantic boundary | Number of comparisons |
| --- | --- | ---: |
| Nat.add, Nat.sub, Nat.mul | Arbitrary-precision unsigned arithmetic and truncated subtraction | 42 |
| Int.add | Signed arbitrary-precision addition | 10 |
| String.append, String.utf8ByteSize, String.length | Unicode UTF-8 append, byte and scalar-value lengths | 24 |
| Array.push, Array.size | Persistent arrays of boxed UInt64, Nat length | 10 |
| List.reverse._redArg | Persistent lists of UInt64 | 5 |
| **Total** | **Ten production IR adapters** | **91** |

The backend additionally recognizes IRType.object, IRType.tobject and IRType.tagged as standalone runtime values, with Expr.box restricted to UInt64, and an erased Arg accepted only at exact Array proof positions. Other heap operations still refuse. The value API is dynamically typed at the Rust boundary; callers must supply the appropriate variant, so this does not prove typed Lean source identity in arbitrary external Rust callers.

`src/standalone_runtime.rs` is embedded into generated source on demand. It has no Lean runtime dependency, no parser or alternative source compiler, and no external Cargo crates. The BigNat/BigInt implementation retains values beyond 512 bits rather than narrowing them to machine integers. Unicode tests include composed/decomposed characters and non-BMP code points.

## Reproduce

With Linux x86-64, Lean 4.34.1 at commit 5045d0056413266e57c625dcd7c365b10e377c52, Rust 1.99.1 and a C compiler:

    cd rust/native_lean_backend
    export LEAN_PREFIX=/path/to/pinned-lean-4.34.1
    lake build
    bash scripts/check.sh

The existing 3,904 Lean-native oracle assertions cover scalar arithmetic boundaries, Boolean branching, direct and mutual recursion, plus refusal preservation. The new source-driven item-30 fixture adds 91 comparisons for large unsigned/signed integers, Unicode, arrays and lists. The **combined 3,995 assertions** compare original Lean results and generated Rust results on identical values. Rust codegen does not consume the oracle values.

The generated Rust runs independently as a Cargo executable in debug and release with Lean runtime environment variables removed. Strict Clippy, unsafe-code prohibition, and dynamic dependency inspection are enforced. The negative fixture requires precise JSON refusals and unchanged output files for unsupported Nat.div, String.push and Array indexing.

## Explicit limits

- Finite differential testing is not a kernel-checked translation theorem or universal semantic correctness claim.
- Generic collections, arbitrary field access, list constructors, mutation and aliasing/reference counts, IO, effects, exceptions, arbitrary Char APIs and malformed UTF-8 are not supported.
- The current Unicode contract covers valid UTF-8 code-point counting, not locale rules, normalization or grapheme clusters.
- Additional Nat/Int operations, arbitrary runtime functions, indirect calls and noncomputable ETH programs remain fail-closed.
- Existing compiler IR budgets do not bound generated-runtime memory use; use OS quotas for hostile inputs.
- PR #202's join-point expansion must reconcile the pinned IR whitelist and tests on integration.
- This item can be checked as complete **only within the explicit published and tested executable-IR feature contract**. It does not close G1 or G2.
