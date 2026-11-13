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
1.99.1, C compiler, `ar`. No Cargo crates are downloaded; there are no
third-party Rust dependencies.

```sh
cd rust/native_lean_backend
export LEAN_PREFIX=/absolute/path/to/lean-4.34.1-linux
./scripts/check.sh
```

`check.sh` builds a Rust shared library and `NativeRust.olean`, then loads the
backend into Lean's interpreter. It compiles **15 isolated declarations and
three transitive closure roots**, generates standalone Rust, and executes
**1,984 independently evaluated Lean/Rust assertions**. It also checks
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
`examples/Library.lean` and `examples/Closure.lean`. This emits a single
Rust source module for **one root**; complete Cargo crate generation and
multiple public roots remain future work.

## Precise coverage

**Implemented and exercised:** functions over `UInt8`, `UInt16`, `UInt32`,
`UInt64`, or `USize`; scalar numeric literals representable as small Lean
`Nat`; `UInt*.add`, `.sub`, `.mul`, `.decEq`, `.decLt`, `.decLe` primitives, parameters,
straight-line local assignments, returns, and Boolean cases whose two arms
have exact `Bool.false`/`Bool.true` constructor identities. Integer arithmetic uses
`wrapping_*`; Lean `Bool` results use the IR's `u8` convention (0/1).
The closure command additionally supports typed direct calls, shared
transitive dependencies, imported executable functions, and direct/mutual
recursion when every reachable body uses supported IR.

**Not implemented:** general Lean/Rust compilation; arbitrary-precision
`Nat`; indirect calls, closures, non-Boolean cases, join points, arrays,
structures, complete standalone crate generation, general external primitives, and
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
