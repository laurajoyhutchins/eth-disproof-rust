# Compiler-IR Rust backend experiment

Status: **opt-in executable-declaration bridge; not an ETH source port**.

The original ETH source is pinned to Lean **4.34.1**. The existing
[leanfran Rust backend](https://github.com/conao3/lean-leanfran) at version
0.6.0 currently requires Lean **4.35.0**. Do not change the original
Lean/Mathlib pins to run this experiment. The independent smoke fixture
has its own Lean toolchain and does not affect the Rust crate.

## Why

Instead of maintaining individual translations for Lean source constructs,
give elaborated compiler IR to an existing Rust backend. The backend
discovers the transitive *executable* declaration closure. Requested roots
identify entrypoints; they are not an expression-constructor allowlist.

The original QueryStreamProgram.program appears under a noncomputable
section. A noncomputable declaration does not necessarily have compiler IR.
Therefore successful generic compilation of a separate executable
declaration says **nothing** about complete ETH source coverage.

Missing IR, skipped declarations, or unavailable runtime externs must be
refused. They cannot authorize a host-side #SAT implementation.

## Running the isolated experiment

The two-path runner is now the native Rust `eth-compiler` binary. It uses the
already-locked `serde`, `serde_json`, and `sha2` dependencies and standard
Rust subprocess/filesystem APIs. It does not require Python.

Install Lean 4.35.0, lake, and leanfran 0.6.0 (generator version 4), then
use an actual Git checkout containing the pinned Lean module and toolchain:

```sh
cargo run --locked --bin eth-compiler -- compile \
  --backend compiler-ir \
  --source-repo /path/to/lean-project \
  --source-revision "$(git -C /path/to/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --lake-root /path/to/lean-project \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --output /tmp/lean-ir-smoke-generated.rs \
  --receipt /tmp/lean-ir-smoke-receipt.json
cargo test --locked --bin eth-compiler
```

The Git source checkout must contain a committed `lean-toolchain`. The
compiler-IR path refuses a Lean 4.34.1 checkout because the currently pinned
leanfran version requires 4.35.0; it does not upgrade the original ETH source.

The Rust integration tests exercise refusal and schema validation; they do
**not** prove real leanfran compilation. The real smoke test still requires
compatible installed Lean/leanfran binaries and generated code compilation.

A successful receipt has status **generated-unverified**, source and toolchain
identity, generator version, declaration roots, backend coverage, generated
SHA-256 and explicit missing semantic and physical proofs. Skipped declarations
or mismatched versions refuse rather than producing an accepted receipt.

Generated Rust requires the leanfran runtime and is not yet linked to the
ETH crate.

## Acceptance path

1. Pin and attribute an exact backend source revision, validate its
   compatibility with the original Lean 4.34.1 without upgrading the
   source/Mathlib pins, and compile an original computable declaration.
2. Compare real original Lean and generated Rust outputs independently;
   check exact Nat and IO semantics.
3. For noncomputable source definitions, introduce a source-independent,
   shared, lazy residualizer over elaborated core expressions. It must
   preserve supported reduction semantics without eager table expansion;
   axioms, opaque externs and unsupported reductions must refuse.
4. Retain symbolic BitProgram construction as a verified specialization.
   Preserve source label layout, PC, ports, transition steps and physical
   relocation against independently executed original Lean traces.
5. Only after all stages pass may the generic backend become the default
   native codegen path for the ETH executable closure.

The source graph exporter remains authoritative for its previously
verified physical graph subset. Compiler-IR source emission and physical
BitProgram correctness are different proof obligations.

Attribution: leanfran, conao3/lean-leanfran, Apache-2.0. The external
backend is not vendored or included as a Cargo dependency in this PR.
