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

## Scoped receipts that can actually be checked

The adjacent [receipt ledger](../evidence/claims.json) describes **three specific compiler claims**: a Lean theorem in an abstract reference-count event model, a bounded source-to-emission event-order guard, and a bounded original Lean C versus generated Rust ownership-event differential. None is a theorem about the complete ETH machine, actual arbitrary Rust execution, or universal runtime equivalence.

Run the source-byte check without network access:

```sh
python3 -m unittest discover -s tools -p 'test_evidence_claims.py'
python3 tools/check_evidence_claims.py --json
```

On an authenticated machine with GitHub Actions read access, independently check the original workflow evidence:

```sh
GITHUB_TOKEN=... python3 tools/check_evidence_claims.py --verify-remote --json
```

The auditor computes the **actual Git blob SHA-1**, including Git's `blob <length>\\0` prefix, for every pinned local proof or implementation file. If any bytes change, the current claim **refuses**, rather than silently inheriting an older passing run. It also rejects duplicate claims, malformed domains, missing exclusions, path traversal, unsupported proof tiers, and a model theorem mislabeled as executable refinement. This is not a whole-repository graph or a GitHub-hosted database.

Remote mode retrieves the actual Actions run and its jobs, requiring an exact matching tested commit, workflow filename, completed successful run, named successful job, and named successful gate step. A green workflow URL or a claimed commit alone is insufficient.

**Semantic boundary:** this authenticates a *specific historical check over exact unchanged bytes*, not the theorem's meaning, compiler correctness, transitive dependency completeness, machine-level behavior or proof validity at a changed source. The claim's quantifier and explicit exclusions remain binding. The auditor's `semantic_promotion: none` field is intentional.

The **root Rust workflow** runs the local refusal suite and content-pin check entirely offline, so ordinary edits cannot inherit stale evidence or become dependent on GitHub API availability. The [scoped evidence workflow](../../.github/workflows/evidence-receipts.yml) checks the actual historical Git trees and Actions run/job/step when the ledger, its validator or its tests change; it can also be invoked manually. Historical run metadata remains subject to GitHub retention, so this is an authenticated receipt mechanism, **not permanent theorem storage**. Adding a new evidence tier, especially an actual Rust-to-Lean universal correspondence theorem, requires a separately specified check and new test cases. The canonical `eth-stage-evidence` implementation-stage graph remains distinct from this scoped compiler receipt ledger.
