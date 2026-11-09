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

## Fast complete checkpoint without losing cases

The full checkpoint runs in **two independent GitHub runner VMs**, not
competing CPU-bound workers on one throttled runner. Each one collects the
unchanged `-m checkpoint` test suite and deterministically owns one half of
the pytest node IDs (SHA-256 partition). Test names and parameters are never
changed, skipped deliberately, or downgraded to integration to improve time.

The terminal required `checkpoint` job consumes both exact-head artifacts,
requires both jobs to have succeeded, compares their source fingerprints and
change-impact plans, independently validates both JUnit files, and checks
the disjoint union of their selected node IDs against the original **entire**
checkpoint collection. Missing, duplicate, stale, or misassigned cases
fail closed. The original single-process verifier and optional native/backend
workflow remain unsharded.

Documentation-only changes still produce a `not_applicable` record from both
shards. Conservatively owned research changes execute their targeted tests
on shard zero, with an explicit `no_assignment` receipt for shard one.
Unknown modifications execute the complete distributed checkpoint.

The checkpoint's 30-second goal measures **slowest shard test execution**.
The total GitHub Actions completion time includes runner scheduling, pip
installation, strict typing, evidence transport, and aggregation, and should
be reported separately. Sharding increases runner concurrency and cost: it is
justified only if an exact full-suite comparison demonstrates a useful speedup.

## Fast exact mathematical certificates

The paper depth-sum contract now supplies an independently checked integer
upper witness `K=s*ceil_sqrt(ceil(p/q))` for each rational ratio `p/q`,
verifies `q*K*K >= p*s*s`, and sums the certified ceilings. This is a
**stronger sufficient inequality** for the original bound. For smaller
parameter instances, the literal enormous-integer square-root oracle is
also retained. No tested paper activation size is removed.

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
