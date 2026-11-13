# Two-path Lean codegen: enforced artifact gate

Status: **code-generation integrity contract, not a semantic refinement proof**.

This is stacked on PR #187, which is stacked on PR #184. The original pinned
ETH source-graph exporter is unchanged. Do not merge this as a completed ETH
compiler or treat its artifact receipts as authorization to execute Rust.

## The one entrypoint

`run_two_path_codegen.py` requires the caller to explicitly select exactly
one backend. It does **not** automatically retry symbolic lowering when compiler
IR is unavailable, and never substitutes a host-side implementation.

| Route | Producer | Success status | Executable? |
| --- | --- | --- | --- |
| `compiler-ir` | Existing leanfran adapter from PR #184 | `generated-unverified` | No |
| `residual-expr` | Generic `Lean.Expr` DAG exporter from PR #187 | `residualized-unverified` | No |
| Either on failure | No artifact receipt | Refused | No |

Before either route can publish an accepted artifact and matching receipt, the
runner requires the **current Git HEAD** to be the specified 40-character commit
and verifies the source file's on-disk bytes equal its Git blob. The
`lean-toolchain` file must likewise be committed and unmodified. For projects
with nested toolchain pins, pass the source-relative
`--source-toolchain-path`.

The actual compiler version is observed via `lake env lean --version` and
checked against the committed source toolchain pin. A compiler-IR receipt must
also claim that *same* pin and observed version. In particular, a Lean 4.35.0
IR fixture cannot be silently attributed to an original Lean 4.34.1 checkout.

The compiler-IR route checks its original backend receipt, source-byte SHA-256,
byte count, exact roots, nonempty function summary, and skipped-declaration
list. The symbolic route checks its versioned JSON, exact original declaration
name, typed Lean core-expression node schema, topological child references,
node bound, and mandatory unverified flags.

Artifacts and receipts are staged together; the receipt is published **last**.
If any stage fails, the new result is refused and any old receipt is deleted.
The caller must verify that the receipt's SHA-256 still matches the artifact
before consuming it. The artifact may remain from a previous run, but it has
no valid acceptance receipt after failure.

## Invocation

For a checked-out Lean project whose tracked source contains the requested
module/declaration (illustrative paths):

```sh
python3 rust/lean_eth_reference/tools/run_two_path_codegen.py \
  --backend residual-expr \
  --lake-root /work/lean-project \
  --source-repo /work/lean-project \
  --source-revision "$(git -C /work/lean-project rev-parse HEAD)" \
  --source-path LeanIRSmoke.lean \
  --module LeanIRSmoke --root LeanIRSmoke.double \
  --producer rust/lean_eth_reference/tools/lean-ir-smoke/ResidualGraph.lean \
  --output /tmp/lean-residual.json \
  --receipt /tmp/lean-residual.receipt.json
```

Replace `--backend residual-expr` with `--backend compiler-ir`, omit
`--producer`, and change the output to `.rs` only when the compatible real
leanfran backend is installed. The compiler-IR route is **not** proven to work
against the original source's Lean 4.34.1 pin; a toolchain mismatch is a hard
refusal.

The independently callable post-generation validator is
`lean_codegen_contract.py`. It requires the same source identity fields plus
an artifact file, and for compiler IR also the backend report.

## What the receipt actually proves

`git_file_matches_head=true` establishes only source **file** integrity; it
does not prove that the Lean declaration came from that file. Even on success:

- `declaration_source_binding=not-established`
- `transitive_executable_closure=not-established`
- `lean_rust_semantic_refinement=not-established`
- `physical_bitprogram_refinement=not-established`
- `executable_approved=false`

The `Lean.Expr` producer's `lean_defeq_checked` flag records a Lean
metaprogram reduction check, not an independently checkable certificate. No
general Lean-to-Rust semantics, noncomputable closure, or ETH disproof follows.

**Important:** the original `run_lean_ir_backend.py` smoke adapter and the
preexisting source-graph exporter can still be run independently. Their
artifacts have not been retroactively verified. A consumer requiring the new
acceptance boundary must require a matching `lean-two-path-contract-v1`
receipt and reject other input.

## Verification evidence

- Offline: 14 regression tests covering both backend payloads, malformed
  JSON/DAGs, Git blob/toolchain mismatch, wrong roots, skipped compiler-IR
  functions, digest mismatch, source mutation, stale receipts and no fallback.
- Local real Lean: `run_two_path_codegen.py --backend residual-expr` successfully
  elaborated an isolated `noncomputable def` on **Lean 4.34.1** and **Lean
  4.35.0**, returning receipts with compiler versions and
  `executable_approved=false`.
- Still **not executed** here: actual leanfran generation, original
  `SqrtLogSpace.QueryStreamProgram.program`, independently verified Lean/Rust
  physical-transition correspondence.

## Next gates

1. Generate a Lean-side declaration provenance witness from the exact original
   `ConstantInfo` and imported module environment, not merely a Git file path.
2. Analyze transitive computational dependencies, including axioms, opaque
   declarations and required external execution primitives, using bounded
   demand-driven reduction.
3. Establish a kernel-checkable expression round-trip or source refinement
   certificate for the residual DAG.
4. Implement a type-checked non-eval Rust consumer and compare its behavior with
   independently executed original Lean states, ports, labels and transitions.
5. Add a verified artifact consumer that refuses any receipt whose
   `executable_approved` bit is false. This pilot deliberately emits **only**
   unverified artifacts.
