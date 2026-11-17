# Complete Lean proof dependency graph

This tool exports actual **elaborated constant dependencies**, not a source import graph
or hand-curated proof diagram. It reads declarations from the compiled
Lean.Environment.checked, follows every constant in each reachable theorem's
elaborated **type** and **proof body**, and preserves external/mathlib and
compiler-generated constant references.

## Original versions

| Source | Commit | Lean | Mathlib |
| --- | --- | --- | --- |
| OpenAI math | 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a | 4.34.1 | d13f23b723b8a846827a245b89c10fc7d3f11612 |
| Anthropic formal-math | 16a5ce41304fcdaea4e0be7c132e1c361dc26da5 | 4.33.1 | 0df444a360eaa60ab8c11dca51a86af692955474 |

OpenAI roots: exact_count_and_sat, exact_count_eth, original_sat_main, QueryStreamProgram.command,
and all three SqrtLog.Execution.Final endpoints (mainTheorem,
binaryIdentifierMainTheorem, fullMainTheorem), under
OAI.Algorithms.SubexponentialSAT.
Anthropic roots: MainResults.mainTheorem and MainResults.ethIsFalse.

## Run on a network-enabled GCP VM or build worker

Clone both upstream repositories at their exact commit pins first.
The OpenAI run deliberately uses the existing narrow
instrumentation/lean-env package from this repo, linking the exact upstream
lean/OAI source tree, rather than the upstream OAI Lake project with dozens
of unrelated mathematical dependencies.
Use elan for the original Lean versions and let Lake restore each pinned
Mathlib package. From this directory execute:

    bash run_pinned.sh openai /work/openai-math /work/output
    bash run_pinned.sh anthropic /work/anthropic-formal-math /work/output

The runner checks source SHA, Lean version, and Mathlib SHA and fails
rather than accepting a substitute. It never edits the original sources.

Results per source:
- original.jsonl (named openai.jsonl or anthropic.jsonl): complete transitive
  declaration closure, one row per real elaborated constant, with type_refs
  and value_refs separately
- source-summary.json: version pins, counts and raw SHA-256
- source-project-graph.json: lightweight projection of project constants and
  their immediate external boundary, with all hidden-library nodes accounted

Load the project-graph JSON into the iPad-friendly Kernel import viewer:
https://lean-proof-explorer.hatchable.site/kernel.html

The browser reads files locally and does not upload them.

## Verification and limitations

No arbitrary depth or node-count caps are applied to extraction.
The terminal completion record is mandatory. The validator fails on
missing roots, missing references, duplicate nodes, count mismatches and
interrupted output.

These are **Lean elaborated constant references**, not tactic steps, runtime
call edges or an independent proof that the formal machine faithfully models
the intended physical computation.

Local smoke test: Lean 4.34.1, 29 reachable declarations, 42 type refs,
59 proof/body refs. Original OpenAI and Anthropic environments have NOT
yet been built and imported in this session. Their complete graph data
must not be claimed ready until both exports and validators finish.

The repository's existing source-graph/Rust parity work is a separate
acceptance tier; this extractor studies formal proof dependencies.

## Manual GitHub Actions runner

The workflow `.github/workflows/complete-lean-proof-graph.yml` is
`workflow_dispatch` only to avoid an expensive Mathlib build on every commit.
It fetches each original source pin, uses the corresponding Lean/Mathlib
version, and uploads separate raw graph, summary, and iPad projection artifacts
for OpenAI and Anthropic. It must run on a networked runner with adequate
GitHub Actions minutes (or be adapted to a GCP worker). It has not yet run
against the pinned originals in this PR.
