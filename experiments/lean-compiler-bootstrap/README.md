# Lean → Rust bootstrap experiment

A standalone acceptance project for replacing the custom native Lean-to-Rust
Reader. This is an experiment, not a second production backend for ETH.

The first **admitted** input is the unmodified upstream Lean 4.34.1 module
`Lean.Compiler.LCNF.Simp.Config`. A narrow `CompilerConfig` facade constructs
the original configuration type and selects four fields over all 256 UInt8
inputs. Official Lean independently generates the expected results. The
generated Rust crate must agree on all 1,024 comparisons.

The more ambitious `Lean.Compiler.IR.Basic` trial is preserved as
`lean/Bootstrap.lean`, but is not currently admitted by lungo: its imported
closure requires four unsupported runtime externs (Lean.Expr.dbgToString,
Lean.Expr.mkData, Lean.profileit, and the manual-root operation). This is
a source-derived **UNSUPPORTED** result, not a successful compiler port.

The machine-checked theorem `CompilerConfig.update_preserves_eta` is registered
as an assurance claim. This checks a property of the original Lean
computation, **not** general Rust semantic or ownership refinement.

## Run

On Linux x86-64 with exact Lean 4.34.1 and Rust 1.99.1:

```sh
export LEAN_PREFIX=/path/to/lean-4.34.1
bash experiments/lean-compiler-bootstrap/scripts/check.sh
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
- Does not replace `compiler` or its CI gates.
- Does not compile the ETH manuscript's noncomputable algorithm.

Next expand to a true compiler transformation from original Lean source,
then borrowed/owned object traces, mutation, imported closure, a Rust-hosted
compiler entrypoint and finally stage-two bootstrapping. Unsupported
behavior must refuse rather than silently substitute another algorithm.
