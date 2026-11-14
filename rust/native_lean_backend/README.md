# Native Lean → Rust compiler backend (initial executable subset)

This is an **in-process code generator**, not a JSON exporter. Lean 4.34.1
elaborates a declaration and compiles it to its normal `Lean.IR.Decl`; the
`#native_rust` command passes that **borrowed IR object** to a Rust `cdylib`
loaded by Lean's `--load-dynlib`. The Rust backend traverses the live object
using tiny accessor functions built against the exact-version `lean.h`, then
emits **standalone, Lean-runtime-independent Rust source**.

```
Lean 4.34.1 -> Lean.Compiler.compile -> Lean.IR.Decl
                                         | (borrowed pointer; no JSON)
                                         v
                              Rust cdylib in Lean process
                                         |
                                         v
                                  generated .rs -> rustc
```

## Tested usage

Linux x86_64, pinned Lean 4.34.1 (including headers and shared runtime), Rust
1.99.1, C compiler, `ar`, and **GMP development headers/library** for
object-valued generated Rust. No Cargo crates are downloaded. The generated
Nat runtime links against system `libgmp`; it does not link Lean. On Ubuntu,
install `libgmp-dev` before running the suite. GMP's library/distribution
license obligations apply independently of this compiler's license.

```sh
cd rust/native_lean_backend
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1-linux
./scripts/check.sh
```

`check.sh` builds a Rust shared library and `NativeRust.olean`, then loads the
backend into Lean's interpreter. It compiles **15 isolated declarations and
three transitive closure roots**, generates standalone Rust, and executes
**11,288 independently evaluated Lean/Rust assertions**, including 256 join-point
cases, 768 multi-root Cargo library cases, 3,072 immutable object
constructor/projection cases, and 5,208 arbitrary-precision `Nat` cases. It also checks
fail-closed behavior, preserved outputs, stable output hashes, Cargo tests,
formatting, and strict Clippy. `lake build`
also builds the Lean module without any Mathlib dependency. The dedicated
GitHub workflow runs these gates only for changes to this backend.

Use the command in a Lean file after importing `NativeRust`:

```lean
namespace Demo
  def addOne (x : UInt64) : UInt64 := x + 1
end Demo
#native_rust Demo.addOne as "add_one" to "examples/generated_add_one.rs"
```

The command requires the `liblean_rust_native_backend.so` to be loaded by Lean.
It intentionally refuses unsupported declarations instead of writing substitute
algorithms.

The additional `#native_rust_closure` command compiles a root together with
its reachable executable dependencies, including imports, **in process**:

```lean
import NativeRust
import Library

def pipeline (x : UInt64) : UInt64 := Library.bump (Library.triple x)
#native_rust_closure pipeline as "pipeline" to "generated_pipeline.rs"
```

The compiler reuses Lean's imported compiler IR, generates collision-free
internal Rust names, checks signatures and calls, and refuses missing or
unsupported dependencies. Example source and test fixtures are in
`examples/Library.lean` and `examples/Closure.lean`. This also supports a complete, standalone multi-root Cargo library:

```lean
#native_rust_package [PackageFixture.pipeline, PackageFixture.combined,
                      PackageFixture.select] to "examples/native-package"
```

The emitted `Cargo.toml` and `src/lib.rs` include the transitive, deduplicated
closure for all requested roots, with one public function per final Lean name
segment. Two roots with the same public segment refuse rather than silently
renaming or overwriting an export. The package has no external dependencies and
is its own Cargo workspace. The destination must not already exist; a new
package is published only after codegen succeeds. It is a **library** crate,
not a user-friendly executable CLI yet.

## Precise coverage

**Implemented and exercised:** functions over `UInt8`, `UInt16`, `UInt32`,
`UInt64`, or `USize`; scalar numeric literals representable as small Lean
`Nat`; `UInt*.add`, `.sub`, `.mul`, `.decEq`, `.decLt`, `.decLe` primitives, parameters,
straight-line local assignments, returns, and Boolean cases whose two arms
have exact `Bool.false`/`Bool.true` constructor identities. Integer arithmetic uses
`wrapping_*`; Lean `Bool` results use the IR's `u8` convention (0/1).
The closure command additionally supports typed direct calls, shared
transitive dependencies, imported executable functions, and direct/mutual
recursion when every reachable body uses supported IR. A restricted class of
**non-recursive typed join points** (`jdecl`/`jmp`) now lowers to lexically
capturing Rust closures, including jumps from Boolean branches. Recursive
joins, non-scalar join parameters, and unsupported runtime operations refuse.

A further opt-in immutable-value subset supports `Option UInt64`, nested
`Option`, and `UInt64 × UInt64` constructions and pattern matching through an
`Rc`-backed generated Rust runtime. See `examples/Objects.lean`. This representation
is not a full Lean runtime: its constructor names and layouts are validated,
and all mutation and observable reference-count primitives remain refused.

**Not implemented:** general Lean/Rust compilation; full `Nat` primitive
coverage or large closed `Nat` constant graphs; indirect calls, closures,
non-Boolean cases, recursive joins, arrays, structures, general external
primitives, and
noncomputable expressions without compiler IR. The current generated functions are checked
on examples but there is not yet a general semantic refinement theorem.

The backend returns `ERROR` for missing types, instructions, operations and
unsupported shapes. Lean fails the command before publishing accepted output.
The source path in `#native_rust` is a caller-supplied destination; the
command publishes code through an atomic rename and leaves prior output
unchanged on failures. Cross-filesystem rename errors refuse instead of
falling back to partial copying. See [COVERAGE.md](COVERAGE.md) for the
versioned IR coverage contract and exact test boundaries.

## Security and maintenance boundary

- ABI layouts and constructor tags are pinned to `Lean.Compiler.IR.Basic` in
  Lean **4.34.1** at commit `5045d005`. The build script checks the exact
  version and commit and rejects non-Linux-x86-64 targets. Upgrading Lean requires auditing these exact layouts and
  rerunning the real integration tests. This is not a stable cross-version FFI.
- The shim accesses borrowed Lean objects synchronously. It does not retain
  pointers or mutate Lean's heap. Rust catches ordinary panics and reports
  failures, but memory safety depends on the exact Lean ABI; run this code in
  an isolated compiler process when processing untrusted code.
- This initial backend uses the pinned native `lean.h` directly rather than
  introducing unpinned `lean-ffi` crate dependencies. Integration with
  `lean-ffi` can replace the shim after checking its Lean-version support.
- The output is not proof-carrying and does not validate the OpenAI ETH source
  theorem or its primitive resource bounds.

This prototype is independent of the 4.35.0 leanfran experiment in PR #184.
It is intended to establish a working in-process ABI and production-quality
fail-closed boundary before extending coverage.

### New G1 conformance fixtures

`examples/JoinFixture.lean` creates real Lean compiler-IR join points and
checks 256 independent Lean/Rust results. `examples/MultiRoot.lean` builds
three public functions into one Cargo crate and checks 768 independent results.
The exact test suite verifies shared dependency deduplication, deterministic
crate emission, public-name collision refusal, unsupported type refusal, and
no modification of previously published directories. These are successful
examples within a **bounded subset**, not proof of general compiler correctness.

### New: exact arbitrary-precision Nat primitives

The generated Rust runtime now represents natural numbers with GMP-backed,
reference-counted immutable values. This supports **Nat.add, Nat.sub, Nat.mul,
Nat.div, Nat.mod, Nat.decEq, Nat.decLt and Nat.decLe**, plus small tagged Nat
constants and arithmetic with them. It does **not** cast Nat to `u64` or
`usize`. Subtraction saturates at zero; division by zero returns zero and
modulo by zero returns the dividend, matching Lean's semantics.

`examples/NatFixture.lean` generates a standalone Cargo library and 5,208
independently Lean-evaluated test assertions over numbers from 0 to 1,024+
bits. The test includes zero divisors, mixed tagged and heap operands, large
products, and boundary comparisons. `RefusalNatBitwise.lean` tests an
unsupported Nat primitive and the absence of partial output.

**Limitations:** This is still a bounded, explicitly supported primitive
subset, not a complete implementation of Lean Nat code generation. Large
*closed* Nat expressions and many additional `Nat` operations remain
unsupported. Public Nat results use the generated `__LeanValue` wrapper;
`nat_from_decimal` and `nat_to_decimal` are the explicit Rust boundary for
this subset. Generated packages containing the immutable-value runtime need
`libgmp` at build and run time. No semantic-preservation theorem is claimed.

### Large compile-time Nat literals and optional GMP

Large integer literals are decoded from **live** `Lean.IR.LitVal.num` values
using Lean 4.34.1's public `lean_nat_div`/`lean_nat_mod` operations in the
version-pinned C shim. No JSON, generated source substitution, or conversion
through a machine word is involved. Constants above 4 KiB of Lean bigint
storage are refused to cap the quadratic decimal extraction cost.

The emitted immutable constructor runtime no longer includes GMP by default.
The generator injects its GMP-backed Nat implementation only when emitted
Rust calls a Nat primitive or constructs a boxed Nat literal.
`Option UInt64`/`Prod` generated tests verify the **linked** executable has
no `libgmp` or Lean runtime dependency. Arithmetic over Nat retains GMP.

`examples/LargeNat.lean` checks 76 independently Lean-evaluated results on
inputs up to 4,096 bits. This handles literal constants, **not** general
constant folding: `Nat.pow` expressions remaining as IR calls still refuse.
