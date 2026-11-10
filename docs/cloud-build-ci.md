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

## Automatic PR verification: one-time activation

**No per-build owner approvals.** The checked-in
[`config/cloudbuild-pr-checkpoint-trigger.json`](../config/cloudbuild-pr-checkpoint-trigger.json)
is a **second-generation GitHub pull-request event trigger** with:

- target base branch `^main# Cloud Build CI transition

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

 and build definition `cloudbuild.yaml`;
- `approvalRequired=false` (no Google approval per invocation);
- `COMMENTS_ENABLED_FOR_EXTERNAL_CONTRIBUTORS_ONLY` (automatic for
  repository owners/collaborators, `/gcbrun` only for outside contributors);
- the existing `engineering-infra-native-ci` build identity, **subject to
  a one-time least-privilege review of project and resource-scoped IAM**.
  That identity exists, but its Google permissions and repository access
  must be verified before reusing it for untrusted PR code.

Cloud Build automatically starts a fresh build on new or updated
eligible PRs after the repository link and trigger are activated. This
does **not** require the ChatGPT GCP bridge's `mcp.tools.call` owner
authorization on each build. That approval boundary applies to *creating
or changing GCP infrastructure*, not to the repository event Cloud
Build is already configured to receive.

**Apply once**, from an owner-authorized environment with the existing
Google identity and `gcloud` (or the equivalent reviewed one-time
GCP mutation through the existing bridge). First inspect whether
`nonexp-sudoku` is already linked. Never create a duplicate trigger or
silently modify an existing one:

```bash
PROJECT=project-6b810532-a302-48dc-b56
REGION=us-west1
CONNECTION=engineering-infra-native-ci
gcloud builds repositories list \
  --connection="$CONNECTION" --region="$REGION" --project="$PROJECT"
gcloud builds triggers list --region="$REGION" --project="$PROJECT"
```

If the repository link is **absent**, link exactly this existing private
GitHub repository to the existing connection once, after confirming the
Cloud Build GitHub App installation can access it:

```bash
gcloud builds repositories create nonexp-sudoku \
  --remote-uri=https://github.com/laurajoyhutchins/nonexp-sudoku.git \
  --connection="$CONNECTION" --region="$REGION" --project="$PROJECT"
```

Then review the pinned build identity's effective permissions, including
bucket-scoped grants; do not widen its project permissions, use the
deployer account or default broad Compute identity, or move untrusted
PR tests onto a private-compiler production credential. When it is
safe, **create this trigger once**, on an accepted reviewed source
containing the manifest:

```bash
gcloud builds triggers create github \
  --trigger-config=config/cloudbuild-pr-checkpoint-trigger.json \
  --region="$REGION" --project="$PROJECT"
```

After creation, inspect the live trigger readback for the exact repo,
`pullRequest.branch`, comment control, service account, enabled
status and disabled build approval. A second normal PR update should
automatically fire a new managed build **without** an owner operation.
Confirm the build's actual commit, clean Git checkout, both checkpoint
shard reports and the GitHub check that Cloud Build posts.

This manifest is a desired configuration, **not evidence of an installed
trigger or sufficient IAM**. The GCP chat bridge's observed trigger
inventory initially contained only a disabled `engineering-infra`
source-observation trigger. That is not the Sudoku trigger and must not
be repurposed. Do not mistake an unrelated successful managed build
for an exact-head Sudoku verification.

## Activate without weakening merge protection

The known GCP project is project-6b810532-a302-48dc-b56 in us-west1.
These coordinates do **not** imply that Sudoku is already connected to Cloud
Build. Use an existing, narrowly scoped GitHub connection for the private
repository laurajoyhutchins/nonexp-sudoku (repository ID 1451517911) or set up
one with explicit owner approval. Do not conflate this with the separate GCE
GitHub-runner approach in engineering-infra#246 and nonexp-sudoku#84.

1. Verify the Cloud Build API, the repository connection, and the existing
   worker's effective IAM. One-time repository authorization may be necessary;
   no per-run Google approval is configured.
2. Apply the reviewed `config/cloudbuild-pr-checkpoint-trigger.json` **once**
   using the exact commands above. It automatically runs for owner/collaborator
   PRs; external contributor PRs require `/gcbrun`. Observe GitHub checks
   rather than assuming check names. Optionally add a separate push-to-main
   trigger once after the PR behavior is proved.
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

Shards run sequentially because Cloud Build steps share /workspace. They have
separate output paths; a missing or failed shard prevents
the aggregate step and fails the build. The 30-second *test execution* target
does not account for Cloud Build scheduling, image downloads or dependency
installation. Benchmark live wall time and cost before calling this faster.

Official documentation:
https://docs.cloud.google.com/build/docs/automating-builds/github/build-repos-from-github
https://docs.cloud.google.com/build/docs/automating-builds/create-manage-triggers
