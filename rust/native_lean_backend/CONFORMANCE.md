# Native Lean 4.34.1 compiler conformance matrix

This is a **versioned, fail-closed contract**, not a proof of general Lean
translation correctness. The native backend uses live pinned Lean IR and emits
standalone Rust. Its conformance gate never serializes compiler IR as an
intermediate compilation representation.

## Reproduce

From the repository root with the exact Lean 4.34.1 installation in
LEAN_PREFIX and Rust 1.99.1, use:

    cd rust/native_lean_backend
    bash scripts/check.sh

The script builds the backend and original Lean example library, then runs
the baseline Lean/Rust fixtures followed by the constructor and primitive
matrix. It writes an exact-source/toolchain receipt to
artifacts/native-smoke-receipt.txt only after every gate succeeds.

## Source-derived constructor inventory

examples/IRInventory.lean inspects the actual Lean environment at build time,
reading the constructors and positions of all these inductive definitions:

| Lean IR family | Constructors | Bounded supported |
| --- | ---: | ---: |
| Decl | 2 | 1 |
| IRType | 14 | 8 |
| Arg | 2 | 2 |
| LitVal | 2 | 1 |
| Expr | 13 | 8 |
| Alt | 2 | 1 |
| FnBody | 13 | 8 |
| **Total** | **48** | **29** |

Bounded-supported `FnBody.jdecl`/`FnBody.jmp` are **only** the tested nonrecursive scalar lexical joins; neither unrestricted recursive joins nor indirect applications are accepted. The source-derived list is emitted to artifacts/ir-constructors.tsv.
scripts/coverage-ledger.rs requires an exact name, tag and supported/refused
classification for **each** constructor in ir-coverage-classification.tsv.
An added, renamed or moved Lean constructor cannot be silently treated as a
previously supported construct. Failures also preserve the previous refusal
rather than publishing partial Rust.

The Rust build script reads the same classification and generates an immutable
whitelist consumed by the production IR decoders. A future implementation arm
cannot cause a previously refused constructor to be accepted until the
classification is explicitly updated. The compiler will continue to refuse
anything outside its supported constructor set. The combined
artifacts/ir-coverage.tsv is a machine-readable release ledger.

The supported entries are *bounded*: e.g. Alt.ctor and FnBody.case mean only
a two-constructor Bool match; LitVal.num accepts only small tagged Nat
literals; IRType.usize has Linux x86-64 semantics. The 19 refused variants
have no positive semantic-equivalence claim. The whitelist test checks tags,
not a theorem about runtime ABI layout or Lean reference counting.

## Source-derived primitive matrix

primitive-registry.tsv is the **single production registry** for supported
fixed-width direct-call primitives; the expression emitter and transitive
dependency scanner both read it.

| Operand families | Operations | Supported combinations |
| --- | --- | ---: |
| UInt8, UInt16, UInt32, UInt64, USize | add, sub, mul | 15 |
| UInt8, UInt16, UInt32, UInt64, USize | decEq, decLt, decLe | 15 |
| **Total** | | **30** |

examples/PrimitiveMatrix.lean declares one genuine Lean function per
registered operation. It invokes the in-process compiler to emit each
function, then computes **64 identical-input expected results per function
using Lean itself**, including equality cases, edge values and seeded values.
scripts/check-coverage.sh rejects a missing fixture or generated function,
compiles all emitted Rust functions into one test binary, and runs all 1,920
assertions. The execution ledger is artifacts/primitive-conformance.tsv.

The existing regression fixtures provide 3,008 additional original-Lean
comparisons over supported scalar, Bool, imported-direct-call and recursive
programs. The candidate combined native suite targets **15,357** Lean/Rust comparisons: 13,336 mainline scalar, join, multi-root, immutable object, function-value and GMP Nat cases; 101 original-source Int/String/collection/Nat cases; and the separate 1,920 fixed-width primitive matrix. The additional 1,024-case randomized Lean/Rust property suite is reported separately.

## Explicit limitations

These tests establish equivalence only for the exercised programs and
supported compiler IR. These tests establish finite comparisons for bounded GMP Nat/Int, Unicode String and collection primitives, but not arbitrary Nat/Int APIs, generic arrays, effects/IO, mutable heap sharing, unrestricted indirect application, recursive join points, or the noncomputable ETH program. Many of those are deliberately refused.

The IR constructor inventory covers the seven pinned *inductive* families;
it does not yet inventory every field of supporting structures such as
Param, VarId, or CtorInfo, nor does it formally verify their C ABI
representations. Separate correctness and ABI obligations remain open.

The feature classification is reviewed, not automatically inferred to be
semantically correct. The automated guards ensure complete enumeration,
prevent unsupported tag acceptance, and require executable evidence for each
registered primitive. They do not turn finite differential tests into a
semantic-preservation theorem.

## Supplementary exact-source value adapters

The production `runtime-primitive-registry.tsv` lists seven non-Nat operations. Three further original Lean Nat functions use the existing GMP primitive dispatcher rather than a second arithmetic implementation. The 101 original-source oracles and refusal-preservation checks run in `scripts/check-item30.sh` using the same in-process compiler. See [SEMANTICS.md](SEMANTICS.md). The 29 supported constructors are conditional on their typed and source-verified layouts.
