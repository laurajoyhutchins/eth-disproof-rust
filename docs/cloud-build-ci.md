# Cloud Build CI transition

These Cloud Build recipes cover the complete pure-Python checkpoint, native
oracles, and seven explicit research and benchmark suites. **Configuration
does not prove that a GitHub trigger exists or has passed.** Keep existing
GitHub Actions checks until the cloud replacement passes on an exact PR
revision and branch protection is updated.

## Build surfaces

- cloudbuild.yaml: main-targeting pull requests and main pushes; strict mypy,
  conservative full impact plan, two independent checkpoint shard processes,
  and exact-source, complete-union aggregation.
- cloudbuild.native.yaml: manual, release, or scheduled native integration;
  Cython, FLINT, Ganak, integration, extended correctness and attestations.
- cloudbuild.research.yaml: explicit _SUITE (cnf-scaling, sudoku-scaling,
  sudoku-representation, unified-cost, valuation-scaling, memory,
  native-cutover); nonrequired benchmarking and research evidence.
- Upstream Lean/Mathlib source-trace stays manual-only in GitHub Actions.

## Activate without weakening merge protection

The known GCP project is project-6b810532-a302-48dc-b56 in us-west1.
These coordinates do **not** imply that Sudoku is already connected to Cloud
Build. Use an existing, narrowly scoped GitHub connection for the private
repository laurajoyhutchins/nonexp-sudoku (repository ID 1451517911) or set up
one with explicit owner approval. Do not conflate this with the separate GCE
GitHub-runner approach in engineering-infra#246 and nonexp-sudoku#84.

1. Verify the Cloud Build API, private GitHub repo connection, and a minimal
   Cloud Build worker identity. No broad GitHub App installation, deploy rights,
   credentials, staging bucket or additional service accounts are assumed.
2. Create a second-generation GitHub PR trigger for target branch ^main$ using
   cloudbuild.yaml. Require /gcbrun approval for untrusted outside contributors.
   Configure direct GitHub status reporting, not a long-lived Actions relay.
   Optionally create a separate push-to-main trigger for the same config.
3. Create explicit/manual release and research triggers, with _SUITE chosen from
   the research script allowlist. Do not mark them required for routine PRs.
4. On a real validation PR, compare the PR head SHA against Cloud Build
   COMMIT_SHA, REVISION_ID and git rev-parse HEAD, require both shard reports,
   and verify that aggregate_checkpoint proves the entire test-file union.
   Check the actual GitHub status context; it is not necessarily named
   checkpoint merely because a Cloud Build step uses that ID.
5. Only after an exact-head successful PR, switch GitHub branch protection
   to the observed Cloud Build check and prove it on another PR. Then disable
   the redundant GitHub-hosted checkpoint and migrate remaining schedules or
   tags. Do not leave a window with no required test gate.

Google Cloud Build commonly checks out shallow source. On integrations that
provide an archive without .git, the recipes **fail closed**. They do not
invent Git commits or silently substitute provider metadata for git provenance.
For private sources, any supplementary Git history fetch must use restricted
credentials. As there is no trusted base SHA in the default trigger variables,
the checkpoint selects full tests instead of taking a potentially unsound
documentation-only or targeted shortcut.

The build logs include SHA-256 digests for the generated JUnit/JSON evidence,
the build ID, and the exact source revision. The raw evidence is **not** yet
persisted to a separately provisioned, generation-pinned GCS bucket. This is
an explicit remaining parity gap relative to Actions artifacts. No evidence
storage permissions or bucket creation are implicit.

Parallel shards have separate output paths; a missing or failed shard prevents
the aggregate step and fails the build. The 30-second *test execution* target
does not account for Cloud Build scheduling, image downloads or dependency
installation. Benchmark live wall time and cost before calling this faster.

Official documentation:
https://docs.cloud.google.com/build/docs/automating-builds/github/build-repos-from-github
https://docs.cloud.google.com/build/docs/automating-builds/create-manage-triggers
