# Repository layout

| Directory | Responsibility | Immediate entry |
| --- | --- | --- |
| [`compiler/`](compiler/README.md) | Generic pinned Lean compiler IR to Rust, admission and conformance | `cd compiler && bash scripts/check.sh` (requires pinned Lean) |
| [`eth/`](eth/README.md) | Original ETH finite-machine port and source-specific execution | `cargo test --locked --offline --all-targets` from root |
| [`experiments/`](experiments/README.md) | Optional Lungo/bootstrap research | `experiments/lean-compiler-bootstrap/scripts/check.sh` |
| [`research/`](research/README.md) | Recursion, parameter bounds, literature and mathematical obligations | Read source and evidence notes |
| `instrumentation/lean-env/` | Lean 4.34.1 and Mathlib acceptance environment | Independent Lean CI |
| `docs/`, `tools/`, `.github/` | Documentation, repository support and CI | MkDocs and path-contract checks |

## Direction of dependence

~~~text
Lean source → existing Lean compiler IR → compiler/ → execution runtime
                                        ↑
                                        | invoked by
                                      eth/

experiments/       independent
research/          evidence and mathematics
~~~

The root Cargo workspace contains `eth/`. The native `compiler/` retains a
**separate Cargo workspace**, because its pinned Lean ABI/header dependency
does not belong in fast general ETH tests. Reorganizations must not silently
combine these toolchain gates.

The general compiler's current implementation is still physically in
`compiler/backend/src/`, including one Reader and its embedded
`runtime/rust/immutable_value.rs`. The proposed
[backend-first architecture](compiler/docs/backend-first-architecture.md)
separates IR lowering from runtime execution. The C **execution** adapter
is not yet implemented; the existing `compiler/frontend/ffi/abi.c` only reads
compiler IR during generation.

The ETH crate currently holds many flat `native_*` modules. Grouping them
into `machine/`, `query/`, `counting/` and `verification/` should follow
independent tests, not be forced into the directory relocation. Likewise
`eth/src/bin/eth-compiler.rs` remains an ETH Cargo binary while delegating
to the canonical compiler. Extracting a standalone CLI is a separate
build-interface change.

The [status ledger](compiler/docs/compiler-status.md) distinguishes
implemented paths from planned ones. G1 original executable Lean
compilation is not G2 residualization of the noncomputable
QueryStream source. A Rust proof kernel would be an independent project.

## Path migration

The current structural change preserves existing file contents and
source commits where possible:

- `rust/native_lean_backend/` → `compiler/`
- `rust/lean_eth_reference/` → `eth/`
- `tools/lean-rust-bootstrap/` → `experiments/lean-compiler-bootstrap/`

The [root agent guide](AGENTS.md) and
`tools/test_repository_layout.py` name the authoritative paths. The
GitHub workflows, MkDocs virtual Markdown mounts, external-project
compiler CLI, and source receipts must all agree before merge.
