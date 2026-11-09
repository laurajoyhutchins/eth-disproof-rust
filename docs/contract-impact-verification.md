# Contract-impact verification

The checkpoint is a correctness gate, not a 30-second timer. Thirty seconds
remains an **observed feedback target**. The runner has a 6-minute safety
limit and `scripts/verify.py` permits 180 seconds for a checkpoint subprocess
to complete before reporting a genuine timeout.

## How the PR/push gate works

1. Checkout the actual change head with full ancestry.
2. Compute changed paths against a trusted Git merge base. A missing base,
   deleted path, malformed diff, or unknown scope selects the **full**
   checkpoint, never a smaller run.
3. Documentation-only changes have an explicit `not_applicable` attestation;
   they do not manufacture successful test counts.
4. Initially, only the isolated `benchmarks/eth/support_join_probe.py` and
   `benchmarks/eth/or_clique_cardinality.py` experiments have owned test
   selection. All lexical consumers are included. Any non-test consumer
   forces full verification. No unowned change is treated as independent.
5. Every other executable change runs the full checkpoint. Strict mypy
   checks execute on every commit regardless of selection.
6. `scripts/verify.py --impact-plan ...` recomputes the plan from the exact
   checkout and rejects stale or modified selection manifests. JUnit and
   evidence still bind to the actual source and verification fingerprints.

On workflow dispatch with no comparison base, verification is comprehensive
by default. The existing weekly `native.yml` job independently runs full
checkpoint, integration, extended, and independent backend-oracle checks.
It is not conditionally skipped based on this PR selection.

## Identical coverage, shorter elapsed checkpoint

The pure-Python checkpoint runner may execute the **same** pytest selection
with four independent `pytest-xdist` workers, scheduled by test file
(`--workers 4`, `--dist=loadfile`). Each test file stays in one worker;
no marker or file is omitted. Pytest checks that workers collect consistent
node IDs; its single JUnit report and ordinary fail-closed evidence still
account for every test outcome. The configured strategy and worker count are
recorded in the verification report.

The separate native, FLINT, and Ganak required-backend jobs remain sequential.
Parallel invocation with a required backend, native attestation, or a
non-checkpoint tier is rejected explicitly: their in-process backend-report
accounting has not been certified for distributed execution. The optional
`checkpoint-parallel` dependency is installed only in the fast CI workflow.
Missing xdist is a test-run failure, not grounds for silently skipping tests.

Local reproducibility:

```bash
python -m pip install -e '.[test,checkpoint-parallel]'
python scripts/verify.py checkpoint --workers 4 --output artifacts/pure
# Reference, identical selected pytest cases but sequential execution:
python scripts/verify.py checkpoint --output artifacts/pure
```

The strict 30-second threshold is never reinstated as a correctness gate.
Time, test counts, skips, failed cases, and evidence stability should be
compared with the sequential reference after every concurrency change.

## Evidence semantics and limitations

Selected tests are actually executed. Tests outside their explicit ownership
boundary are **not** claimed to have passed at the new head.
`reused_evidence: false` is deliberate: this stage does not attempt to
inherit older proofs across commits. General source dependency closure,
transitive/dynamic imports, fixture effects, native build interfaces, and
environment provenance have not been certified for reuse.

The selection model is deliberately narrow until its dependency declarations
can be audited. This avoids introducing a broad, unsound import heuristic
that silently skips an affected test. A later RelGit-style contract graph
can expand the ownership relation and enable verified reuse only when the
whole dependency fingerprint and assumptions are unchanged.

Tests in `tests/unit/test_change_impact.py` exercise documented-only,
selected research consumers, unowned callers, unknown inputs, deletions, and
Git merge-base behavior. The planner itself and CI configuration always
fall back to complete verification.

### Local commands

```bash
python scripts/change_impact.py --base "$(git rev-parse HEAD~1)" --output artifacts/impact.json
python scripts/verify.py checkpoint --impact-plan artifacts/impact.json --output artifacts/pure
# Independently force the complete checkpoint:
python scripts/verify.py checkpoint --output artifacts/pure
```
