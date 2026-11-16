# Lean → Rust bootstrap experiment

A standalone acceptance project for replacing the custom native Lean-to-Rust
Reader. This is an experiment, not a second production backend for ETH.

The input comes from **unmodified upstream Lean 4.34.1**
`Lean.Compiler.IR.Basic`. A thin `Bootstrap` module calls six of its
compiler type predicates over all 256 `UInt8` inputs. The original Lean
toolchain generates 256 independently evaluated rows. A Rust crate built by
pinned `machinefabric/lungo-rs` compares 1,536 results against them.

The machine-checked theorem `Bootstrap.scalar_not_reference` is registered
as an assurance claim. This checks a property of the original Lean
computation, **not** general Rust semantic or ownership refinement.

## Run

On Linux x86-64 with exact Lean 4.34.1 and Rust 1.99.1:

```sh
export LEAN_PREFIX=/path/to/lean-4.34.1
bash tools/lean-rust-bootstrap/scripts/check.sh
```

The script clones the reviewed upstream lungo commit into ignored
`.vendor/` and refuses a modified or wrong checkout. For Lake it copies the exact
Lean sources and overrides only their package toolchain pin to 4.34.1;
Cargo consumes the exact Git revision directly. It builds an original
Lean oracle, compiles the corresponding executable Lean IR through lungo,
runs Rust differential tests and Clippy, and records an evidence receipt.

The project owns its Cargo workspace and has no dependency on the ETH
reference crate. It can be moved into its own repository unchanged.

## Boundaries

- Does not run Lean's compiler driver in Rust.
- Does not establish self-hosting or a stage-two reproducible build.
- Does not establish reference-count or resource-bound equivalence.
- Does not replace `rust/native_lean_backend` or its CI gates.
- Does not compile the ETH manuscript's noncomputable algorithm.

Next expand to a true compiler transformation from original Lean source,
then borrowed/owned object traces, mutation, imported closure, a Rust-hosted
compiler entrypoint and finally stage-two bootstrapping. Unsupported
behavior must refuse rather than silently substitute another algorithm.
