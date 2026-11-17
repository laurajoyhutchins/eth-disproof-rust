# Lean compiler CLI

This Cargo package owns the **one** public compiler interface and
artifact-identity contract. It depends only on pinned Rust libraries.
It does not link or import the ETH counting crate.

From the repository root:

```sh
cargo test --locked --offline --manifest-path compiler/cli/Cargo.toml -p lean-compiler-cli
cargo run --locked --offline --manifest-path compiler/cli/Cargo.toml \
  --bin lean-rust-compiler -- compile --backend compiler-ir \
  --source-repo /absolute/path/to/source-repo \
  --source-path path/within/repo/Sample.lean \
  --source-revision EXACT_GIT_COMMIT \
  --source-toolchain-path path/within/repo/lean-toolchain \
  --lake-root /absolute/path/to/lean-project \
  --module Sample --root Sample.inc \
  --output /absolute/path/to/new/generated-project \
  --receipt /absolute/path/to/new/receipt.json
```

The pinned Lean distribution must be installed in the environment and
`LEAN_PREFIX` must point to it. The compiler-IR route requires
Lean 4.34.1 and invokes `compiler/scripts/compile-project.sh`,
which uses the one in-process IR emitter. The output is an existing
Cargo project plus a separate checked receipt. Unavailable IR and
unrecognized runtime semantics refuse compilation rather than
falling back to a symbolic substitute.

`compiler/cli/src/interface.rs` owns argument parsing, subprocess
budgets, atomic staging and publication. `contract.rs` owns source
identity, artifact receipts, and refusal rules. `compiler/backend/`
owns generated Rust. No code in this package implements or claims
G2 original noncomputable QueryStream execution.

The previous `eth-compiler` command remains a delegating wrapper
for existing tests. Implement changes **here**, not in that wrapper.
