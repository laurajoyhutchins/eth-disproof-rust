# Two-path Lean codegen acceptance contract

Status: **Rust implementation, unverified generated artifacts**. This work is
stacked on the compiler-IR and core-expression PRs. It does not prove the ETH
counting machine executable.

## One Rust frontend

`eth-compiler` provides two subcommands:

- `compile`: run a selected Lean or leanfran producer, validate the output,
  and publish the artifact and corresponding unverified receipt.
- `verify`: inspect an existing artifact and optional IR backend report against
  the same source and schema contract. No code is generated or executed.

The backend is explicitly `compiler-ir` or `residual-expr`; a failed route
**never** runs a different algorithm. This opt-in routing is intentional while
there is no proven cross-backend semantic substitution rule.

Implementation: `src/bin/eth-compiler.rs` and `src/lean_codegen.rs`. This
code uses **existing locked dependencies only**: Serde for typed graph/receipt
validation, serde_json for JSON, sha2 for SHA-256, and standard Rust process,
filesystem and timing APIs. No bespoke JSON syntax, Python orchestration, or
new crate lock entries.

## Reproducible execution

For a Git-pinned Lean project with an actual module and a committed
`lean-toolchain` file:

```sh
cargo run --locked --bin eth-compiler -- compile \
  --backend residual-expr \
  --source-repo /work/lean-project \
  --source-revision "$(git -C /work/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --lake-root /work/lean-project \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --producer rust/lean_eth_reference/tools/lean-ir-smoke/ResidualGraph.lean \
  --output /tmp/lean-residual.json \
  --receipt /tmp/lean-residual.receipt.json
```

To run compiler IR, use `--backend compiler-ir`, omit `--producer`, and
choose a Rust output path. This requires actual `leanfran 0.6.0`,
generator version 4 and Lean 4.35.0, **not** the original Lean 4.34.1
source tree. No automatic upgrade or fallback is allowed.

To validate an artifact without running Lean:

```sh
cargo run --locked --bin eth-compiler -- verify \
  --backend residual-expr \
  --source-repo /work/lean-project \
  --source-revision "$(git -C /work/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --artifact /tmp/lean-residual.json \
  --receipt /tmp/lean-residual.receipt.json
```

Compiler-IR verification additionally requires `--backend-report` containing
the original generation summary. The standard binary runs all lightweight
contract tests under `cargo test --locked --offline --all-targets`.

## Enforced integrity and failure behavior

Before accepting either route, the runner checks:

1. Git HEAD equals the specified 40-hex revision; the source file and
   toolchain pin bytes match their committed Git blobs.
2. The observed Lean version matches the pinned source toolchain during
   compilation. The IR route verifies the expected leanfran/generator version.
3. Backend report/root identities, artifact SHA-256, byte length and missing
   declarations or skips are checked.
4. Residual graphs are decoded with typed Serde enums, strict unknown-field
   rejection, duplicate JSON-field rejection, topological references,
   bounded node counts, and exact source root.
5. Accepted artifacts are staged; the receipt is published last. Any failed
   invocation removes an old acceptance receipt. Consumers must recheck the
   receipt digest before using the corresponding artifact.

The output explicitly retains:

```json
{
  "executable_approved": false,
  "checks": {
    "declaration_source_binding": "not-established",
    "transitive_executable_closure": "not-established",
    "lean_rust_semantic_refinement": "not-established",
    "physical_bitprogram_refinement": "not-established"
  }
}
```

The above is an excerpt of the receipt, not a complete example. The Git blob
proves the checked **file** identity, not that the named Lean declaration
originated in that file or that its dependencies are computationally safe.
The symbolic producer's `lean_defeq_checked` flag is not a standalone
kernel-checkable certificate.

## Outstanding technical obligations

- Build a genuine Lean declaration provenance witness and a transitive
  computational dependency closure (including critical axioms and externs).
- Establish source-preserving demand-driven delta/iota reduction without
  forcing astronomical `Fin l -> Instr` tables.
- Construct a typed Rust residual-expression consumer and prove/independently
  test every accepted operation against the original Lean semantics.
- Demonstrate original ETH BitProgram label, PC, port, transition and cost
  correspondence. A successful Rust compilation is not that proof.

The existing ETH-specific source-graph exporter retains its separately
established physical-graph slice and has not been removed.
