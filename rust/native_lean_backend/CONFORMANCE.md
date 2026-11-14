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
| IRType | 14 | 9 |
| Arg | 2 | 2 |
| LitVal | 2 | 1 |
| Expr | 13 | 8 |
| Alt | 2 | 2 |
| FnBody | 13 | 8 |
| **Total** | **48** | **31** |

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
x86-64 semantics. The 17 refused variants
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

The integrated regression fixtures now provide **16,521** independently
original-Lean-evaluated Rust comparisons: 3,008 scalar/Bool/joins/multi-root,
3,072 immutable Option/Prod, 2,048 source-defined boxed closure/PAP/AP, 5,208 GMP-backed arbitrary-width Nat tests, 3,008 extended Float/enum/unsigned cases, 101 additional original-Lean Int/Unicode/collection/closure operations, and 76 separately Lean-evaluated large closed Nat literal comparisons. Together with the separate 1,920
fixed-width primitive matrix assertions, this is **18,441** compared results.
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

## Extended scalar and executable G1 layer (PR #221)

The same production `primitive-registry.tsv` expands to **68** source-approved operation names: 30 original unsigned add/sub/mul/comparisons, 35 total unsigned div/mod/bitwise/width-masked shifts, and 3 precisely scoped finite Float add/sub/mul operations. The original 30 × 64 independently evaluated Lean fixtures are retained; the 38 additional primitive calls have dedicated source-derived Lean/Rust fixtures, including zero divisors and wide shift counts. Unsupported Float transcedentals, NaN-specific equivalence and nontrivial casts remain refused; finite dyadic operand tests alone cannot prove IEEE behavior generally.

The exact IR whitelist contains **30 bounded-supported / 18 explicitly refused** constructors: it retains the immutable Option/Prod + PAP/AP semantics from #216 and adds only `IRType.float` (finite scalar) and `Alt.default` (nullary UInt8 enum default), with layout validation for scalar constructors. A standalone Cargo binary is generated only from zero-argument scalar roots and checked without a Lean runtime. Neither a checked constructor tag nor a finite differential test establishes general Lean semantic preservation.

The runtime backing these tests is the canonical post-#218 `src/runtime/immutable_value.rs` with GMP-backed `Nat` and `Rc`-backed immutable values. The compiler maintains a single Rust codegen/FFI path. The #221 subsystem has passing exact-head and post-merge checks; additional Int/Unicode/collection adapters require their own integrated-head CI. Three unchanged independent Lean source projects must still compile successfully into standalone Rust before the G1 release claim.

## Supplemental source-defined value adapters (candidate G1 acceptance)

The canonical `src/runtime/immutable_value.rs` is extended with seven source-identified adapters: `Int.add`, `String.append`, `String.utf8ByteSize`, `String.length`, `Array.push`, `Array.size`, and `List.reverse._redArg`. An additional **101** original Lean differential cases cover signed GMP integers, UTF-8 including embedded NUL, immutable arrays/lists, and exact Nat closure calls. The Nat operations reuse the existing GMP implementation rather than a second arithmetic kernel.

`Lean.IR.Arg.erased` is conditionally admitted **only for the source-verified type-proof operand of listed Array externs**. All other erased runtime arguments still refuse. This raises the source-checked bounded constructor whitelist from 30 to **31 of 48**. This acceptance does not imply general Lean heap/exception/IO support or successful independent upstream project compilation. Source-to-Rust CI must pass the combined head before this scope is considered verified.

## Closed arbitrary-precision Nat literals (candidate)

The pinned Lean C API converts source `Lean.IR.LitVal.num` objects to decimal without machine-word truncation; emitted Rust constructs the same canonical GMP-backed `__LeanValue::nat_from_decimal`. Constants with more than 4 KiB of Lean integer storage refuse. `LargeNat.lean` supplies **76** original-Lean oracle comparisons, including large literals and up to 4096-bit external inputs; unknown `Nat.pow` remains a structured refusal. No competing generated GMP runtime is introduced. This feature requires a clean exact-head and post-merge acceptance run.
