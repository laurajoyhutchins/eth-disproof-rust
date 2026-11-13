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

`check.sh` builds a Rust shared library; builds `NativeRust.olean`; loads it into
Lean's interpreter; invokes a real Lean compilation for five declarations;
writes Rust files through `#native_rust`; compiles and runs the standalone Rust
program with `rustc`; checks overflow; checks three refusal cases; and runs
`cargo test`, formatting, and strict Clippy.

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

## Precise coverage

**Implemented and exercised:** functions over `UInt32`, `UInt64`, or `USize`
(with the initial example suite exercising `UInt64`), scalar numeric literals
representable as small Lean `Nat`, `UInt*.add`, `.sub`, `.mul`, parameters,
straight-line local assignments, and return. Fixed-width arithmetic uses
`wrapping_*`, matching those Lean operations.

**Not implemented:** general Lean/Rust compilation; `Nat` big integers; Bool
or branches; recursion, closures, cases, join points, arrays, structures;
transitive dependency closure; external primitives; and noncomputable
expressions without compiler IR. The current generated functions are checked
on examples but there is not yet a general semantic refinement theorem.

The backend returns `ERROR` for missing types, instructions, operations and
unsupported shapes. Lean fails the command before publishing accepted output.
The source path in `#native_rust` is a caller-supplied destination.

## Security and maintenance boundary

- ABI layouts and constructor tags are pinned to `Lean.Compiler.IR.Basic` in
  Lean **4.34.1**. Upgrading Lean requires auditing these exact layouts and
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
