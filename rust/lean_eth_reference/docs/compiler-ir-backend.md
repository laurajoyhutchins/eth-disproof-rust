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

Install Lean 4.35.0, lake and leanfran 0.6.0, generator version 4.

~~~sh
cd rust/lean_eth_reference/tools/lean-ir-smoke
lake build
cd ../../../..
python3 rust/lean_eth_reference/tools/run_lean_ir_backend.py \
  --lake-root rust/lean_eth_reference/tools/lean-ir-smoke \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --output-rs /tmp/lean-ir-smoke-generated.rs \
  --report /tmp/lean-ir-smoke-report.json
python3 -m unittest discover -s rust/lean_eth_reference/tools \
  -p test_lean_ir_backend.py -v
~~~

The independent local test suite exercises a *mock* backend and is not a
real Lean compilation. The real smoke experiment above requires a separate
Lean/leanfran installation, which must pass before claiming Rust generation
from genuine Lean compiler IR.

On success the report status is **generated-unverified** with toolchain
identity, generator version, selected roots, backend coverage summary,
generated source SHA-256 and explicit missing semantic/physical receipts.
Any omitted requested root, backend skip, invalid summary, version mismatch
or failed command yields **refused**, never partial successful output.

Generated Rust requires the leanfran runtime and is not yet linked to
this ETH crate.

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
