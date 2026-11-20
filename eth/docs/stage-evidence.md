# Read-only source-stage evidence graph

This report is a view of the existing [source-stage registry](../src/remaining/registry.rs) and [pinned upstream source manifest](../reference/source-manifest.json), **not** another stage catalogue or a proof certificate.

Run from the repository root:

```sh
cargo run --locked --offline -p lean-eth-reference --bin eth-stage-evidence -- --json
```

The JSON output provides each stage's canonical name, original Lean symbol, original source file and local Git blob pin, machine kind, Rust implementation status, and prerequisite stage IDs. It also lists the currently non-executable stages reachable from `query_stream` and `counting_program`, in source-registry order. A `partial` or `noncomputable` stage is a blocker for completing the original path.

The status `executable` **only means an independently runnable Rust fragment is recorded in the existing registry**. It does **not** mean the compiled Rust has been proved equivalent to the original Lean source, that an original-Lean trace was compared, or that a TM2 resource theorem applies. Accordingly, every stage is reported as `unassessed` for:

- `lean_rust_correspondence`;
- `physical_runtime_correspondence`;
- `tm2_resource_correspondence`.

The report uses `pin_check: local_manifest_shape_only`: it checks the pinned repository and revision, the presence and syntax of all referenced file-blob hashes, unique stage IDs and topological dependencies. It does **not** fetch Git objects or prove that the file contents match the claimed hashes. Existing [source-manifest tests](../tests/remaining_tdd.rs) remain authoritative for the local catalogue contract. Actual source execution and universal cross-language refinement require independent evidence.

## Why the report is deliberately conservative

The source tree has multiple kinds of evidence whose quantifiers differ: Rust tests, original-Lean differential traces, checked Lean mathematical statements, and independent source-derived Rust translation. Combining them into a green flag would be unsound. A source-bound claim needs an exact Rust commit, precise admitted domain, type of observation, and an independently checkable receipt. **No receipt is inferred from a Rust stage name or status.**

The report can be used as the **implementation-side join key** for later provenance relations, without putting a second implementation-status file in the repository. Record proof references separately, with their own domain and exact checked source revision. Do not automatically promote independent artifact existence to end-to-end correctness.

## Deep verification dependencies

The [source-refinement workflow](../../.github/workflows/lean-source-refinement.yml) must rerun its kernel-checked physical-program certificate when its **shared physical instruction encoder** or other `eth/src/bit_program/` helper changes. Its pull-request path filter now covers that directory, not only selected legacy files. [Repository layout tests](../../tools/test_repository_layout.py) defend against accidentally losing this trigger.

Root Rust CI executes the report's unit tests as part of `cargo test --locked --offline --all-targets`. The deep Lean job remains independent: a passing Rust report test does not certify a generated Lean receipt.

See [existing coverage and evidence](evidence.md), [remaining source path](remaining-lean-port.md), and [cross-language acceptance](../../research/lean-rust-acceptance.md).
