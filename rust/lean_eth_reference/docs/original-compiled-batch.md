# Source-compiled Lean programs to executable Rust

**Pinned source:** `openai/math@4eaee87548250b2682affda7d05d947c05554bae`  
**Compiler:** Lean 4.34.1; **Mathlib:** `d13f23b723b8a846827a245b89c10fc7d3f11612`  
**Runtime:** Rust 1.99.1, `lean_eth_reference` physical `BitProgram` implementation

The existing extractor compiled 65 original Lean programs whose instruction tables
are visibly literal source syntax. The remainder frequently uses `compiled`
functions that combine `Cmd.seq`, `Cmd.call`, `Cmd.while`, and `Cmd.ite` with
source-defined register and stack embeddings. Searching those expressions and
transcribing their control flow into Rust by hand is unnecessary: let **the
original Lean elaborator** compute the finite instruction table first.

## Discovery, not proof

`tools/extract_compiled_catalog.py` scans the immutable source tree and finds
closed candidate declarations of the form `def x := compiled ...`. In the
pinned snapshot it found **316 candidates in the QueryStreamProgram import
closure**, **626 across the SAT tree** and **one unsupported lexical scope**.
These are potential exports, not source-authenticated instruction tables,
Rust implementations, Lean/Rust equivalence tests, or ETH complexity results.

`tools/export_compiled_batch.py` selects a bounded subset and refuses each
candidate independently when compilation, elaboration, finite-machine type
checking, resource budgets, source identity, or opcode reduction fails.
It computes the original source Git blob and verifies the pinned Git source,
Mathlib revision and Lean toolchain. The actual `Lean.Meta.whnf` exporter is
`tools/export_source_program.lean`, tested on an independently compiled
standalone Lean 4.34.1 physical program.

Each successful export has a complete ordered `PIN`/`PROGRAM`/`CODE`/`END`
source table and an SHA-256 receipt. The parser checks all twelve source
instruction constructors, dimensions, finite ports, source entry, finite
registers, stack indices and labels. No partial table is accepted.

`tools/compile_exported_batch.py` rechecks each receipt and table's exact
SHA-256 and ABI, calls the Rust program `lean-original-codegen` using the
existing chunked `tools/lean_table_codegen.rs` compiler, and type-checks
**the generated Rust functions** in a separate real Cargo crate. It creates
no host-side SAT evaluator. Failed programs have explicit refusal records and
no retained success outputs.

## Reproduce on public GitHub Actions

The `.github/workflows/original-compiled-batch.yml` runs **offline Python
regressions only** on relevant pull requests. The expensive source compilation
is `workflow_dispatch` only, with a selectable declaration regex, program
limit (default one), and per-program timeout. It runs on public GitHub-hosted
`ubuntu-24.04` with the original pinned Lean+Mathlib cache. GitHub exposes
manual dispatch after the workflow is present on the default branch.
The initial large-target attempt (#43041032199) exported **zero** original
programs: three reduction heartbeat refusals (200,000 default heartbeats)
and one module-build timeout (900 seconds). The next bounded batch instead
selects seven smaller, source-defined targets: two `SqrtLog.Setup` programs
and five `SparseFrontierProgram` commands in the query import closure.
Lean has a 2,000,000-heartbeat deterministic limit and subprocesses still
have a 240-second wall-clock limit per operation. The job shares a pinned
OAI dependency-build cache with the full-query exporter, but cached compiler
outputs do not count as exported programs or semantic verification.

The exporter writes an atomic `batch-report.json` checkpoint before and
after each attempted declaration. Interrupted runs retain validated individual
tables and receipts, and retries reuse them after independently checking their
source identity, ABI, exact SHA-256, Lean/Mathlib versions, and exporter code
fingerprint. Existing partial success does not transform a refused export into
a success. Successful generated Rust, refusal details and reports are retained
as workflow artifacts, not theorem evidence.

Locally, in a checkout with the pinned original Lean source and a working
minimal Lake project (as established by original exporter PR #145):

```sh
cd rust/lean_eth_reference
python3 tools/extract_compiled_catalog.py \
  --upstream /path/to/openai-math --query-closure --output /tmp/compiled-candidates.json
python3 tools/export_compiled_batch.py \
  --upstream /path/to/openai-math --lake-root ../../instrumentation/lean-env \
  --output-dir /tmp/original-compiled --query-closure \
  --name-regex 'SqrtLog\.Setup\.(computeLProgram|logSuccProgram)|SqrtLogSpace\.DisjointReuse\.SparseFrontierProgram\.(pushProgram|initFrontierProgram|popProgram|popIfPresentProgram|pushPairProgram)' \
  --limit 7 --max-labels 4096 --timeout-seconds 240
python3 tools/compile_exported_batch.py \
  --tables /tmp/original-compiled --rust-output /tmp/original-compiled-rust \
  --typecheck-crate /tmp/original-compiled-check --rust-crate . \
  --max-labels 4096
```

## Verification boundary

- The 65 existing literal programs are compiled Rust and tested against an
  independent local Rust interpreter. This does not establish genuine
  imported-Lean traces for those programs.
- A successful new batch is **source-derived Rust**, tied to the original
  elaborated compiled instruction table, but full-state Lean/Rust parity still
  requires an *independent Lean physical execution* of that same program.
- A `PIN` line by itself proves nothing. Source and toolchain checks plus a
  receipt must be checked independently, and artifact integrity must be
  established before results are reused.
- The complete original `QueryStreamProgram.program` and
  `Native.countingProgram` may be too large or partly noncomputable. Budget or
  reduction refusal is an honest result. Smaller subprogram success does not
  establish a nonexponential #SAT counter, a primitive TM2 bound, or the ETH
  theorem.

## Resumable local development

From the repository root, after restoring the pinned original OpenAI source
and Lean 4.34.1/Mathlib project:

```sh
python3 rust/lean_eth_reference/tools/lean_rust.py doctor
python3 rust/lean_eth_reference/tools/lean_rust.py list --filter membership
python3 rust/lean_eth_reference/tools/lean_rust.py build PROGRAM_ID
python3 rust/lean_eth_reference/tools/lean_rust.py status PROGRAM_ID
```

The `doctor` command checks existing source, Lake, Mathlib and Lean pins
without fetching or modifying them. `build` exports, generates and type-checks
one selected declaration, reusing validated tables where possible. `status`
prints a compact developer view; use `status PROGRAM_ID --json` for scripts.
For targeted stages, use `export PROGRAM_ID` and `generate PROGRAM_ID`.

`verify PROGRAM_ID` currently refuses explicitly. Exporting and type-checking
do **not** compare independently executed Lean and Rust machine-state traces.

Use `--upstream`, `--lake-root` and `--output-dir` before the subcommand
to override local paths. The default output is `.lean-rust/`, keyed by pinned source, declaration
and exporter code fingerprint. The driver reuses a cached table only after
checking pinned source and toolchain identity, exporter fingerprint, receipt,
SHA-256, and canonical instruction ABI.
A failed export does not produce a success receipt. Generation still invokes
the strict receipt-checking compiler. `build --verify` deliberately refuses:
independent Lean/Rust machine-state differential verification has **not** yet
been connected to this entry point. Do not interpret typechecking as parity.

This initial entry point is Python orchestration around existing Python/Lean
tools. A Rust clap front end may replace its user interface without duplicating
the exporter or source-table validator.
