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
| Arg | 2 | 1 |
| LitVal | 2 | 1 |
| Expr | 13 | 8 |
| Alt | 2 | 1 |
| FnBody | 13 | 8 |
| **Total** | **48** | **28** |

Bounded-supported `FnBody.jdecl`/`FnBody.jmp` are **only** tested nonrecursive typed lexical joins. The separate `Expr.pap`/`Expr.ap` implementation supports only exact statically compiled, boxed capture/argument signatures; unrestricted recursive joins and arbitrary indirect calls remain refused. The source-derived list is emitted to artifacts/ir-constructors.tsv.
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
an exact two-constructor Bool or Option match; Expr.ctor/proj/box/unbox and
Expr.pap/ap require verified immutable object/boxed closure metadata.
LitVal.num accepts only small tagged Nat literals; IRType.usize has Linux
x86-64 semantics. The 20 refused variants
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

The integrated regression fixtures now provide **13,336** independently
original-Lean-evaluated Rust comparisons: 3,008 scalar/Bool/joins/multi-root,
3,072 immutable Option/Prod, 2,048 source-defined boxed closure/PAP/AP, and
5,208 GMP-backed arbitrary-width Nat tests. Together with the separate 1,920
fixed-width primitive matrix assertions, this is **15,256** compared results.
The additional 1,024-case randomized Lean/Rust property suite is reported
separately. These counts describe different tested subsets, not universal
compiler equivalence.

## Explicit limitations

These tests establish equivalence only for the exercised programs and
supported compiler IR. They do **not** establish general Nat/Int, Unicode
Strings, Arrays, effects/IO, observable heap sharing, arbitrary indirect
application, recursive join points, or the source-defined
noncomputable ETH program. Many of those are deliberately refused.

The IR constructor inventory covers the seven pinned *inductive* families;
it does not yet inventory every field of supporting structures such as
Param, VarId, or CtorInfo, nor does it formally verify their C ABI
representations. Separate correctness and ABI obligations remain open.

The feature classification is reviewed, not automatically inferred to be
semantically correct. The automated guards ensure complete enumeration,
prevent unsupported tag acceptance, and require executable evidence for each
registered primitive. They do not turn finite differential tests into a
semantic-preservation theorem.
