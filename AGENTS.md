# Repository navigation for coding agents

**Compiler:** `compiler/` is the canonical Lean 4.34.1 compiler-IR to Rust
backend. Lean remains the parser, elaborator and compiler. The current Rust
emitter lives in `compiler/backend/src/lib.rs` and `compiler/backend/src/reader/`, reads
borrowed IR through `compiler/frontend/ffi/abi.c`, and embeds a bounded value
runtime from `compiler/runtime/rust/immutable_value.rs`. That runtime is not
verified as a general replacement for Lean C.

**Public compiler CLI:** `compiler/cli/` is a standalone Rust crate, with the original
artifact contract and native Lean-IR CLI. Its binary is `lean-rust-compiler`.
`eth/src/bin/eth-compiler.rs` only delegates for compatibility; no ETH source
module participates in the canonical compiler. Build and test it with
`cargo test --locked --offline --manifest-path compiler/cli/Cargo.toml -p lean-compiler-cli`.

**ETH implementation:** `eth/` is the source-pinned finite machine, research
execution engine and original ETH-specific source compiler. It is the root
Cargo workspace member. The `eth-compiler` CLI currently lives in
`eth/src/bin/eth-compiler.rs` and dispatches to `compiler/`. This is a
documented extraction seam, not authorization for a second backend.

**Experiments:** `experiments/lean-compiler-bootstrap/` tests Lungo on
original Lean compiler declarations. It is neither a production backend
nor a G1/G2 gate. Do not route unsupported Lean IR through Lungo.

**Math and proofs:** `research/` and `eth/proofs/` contain mathematical
analysis and Lean proof obligations; `instrumentation/lean-env/` pins
the Lean/Mathlib acceptance environment. A successful compiler
integration does not prove the ETH counting theorem.

**Documentation:** `docs/repository-layout.md` describes physical and
planned seams. `compiler/docs/backend-first-architecture.md` defines the
execution/runtime order. Do not claim that the future C execution adapter
or Rust-native runtime is already implemented.

## Change rules

- Keep compiler changes independent of `eth/` internals. The ETH crate may
  invoke the compiler, never vice versa.
- Preserve exact pinned Lean sources, kernel evidence, source identities,
  ownership operations and fail-closed refusals.
- Keep the root workspace (ETH) and nested compiler workspace separate
  until an independently verified integration supersedes them.
- Every structural change must update workflows, Cargo paths, Lake paths,
  provenance receipts and MkDocs navigation together. Run
  `python3 -m unittest discover -s tools -p 'test_repository_layout.py'`.
- For ETH: `cargo test --locked --offline --all-targets` at the root.
  For the native compiler: from `compiler/`, use the pinned Lean
  environment and `bash scripts/check.sh`. These are different gates.
- Do not replace the original noncomputable QueryStream construction
  with a guessed Rust counter or silently fall back to brute force.
