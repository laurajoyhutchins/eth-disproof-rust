# Cloud Build CI

Routine checkpoint verification runs in Google Cloud Build in project `project-6b810532-a302-48dc-b56`, region `us-west1`. The repository is linked through the `engineering-infra-native-ci` connection.

- `nonexp-sudoku-pr-checkpoint` runs `cloudbuild.yaml` on pull requests targeting `main`. Owner and collaborator updates run automatically; outside contributors require an authorized `/gcbrun` comment.
- `nonexp-sudoku-main-checkpoint` runs the same recipe on pushes to `main`.
- Both triggers use the dedicated `nonexp-sudoku-pr-ci` service account, with Cloud Logging write permission. They do not use a shared CI bucket identity.

The recipe verifies the exact Git commit, runs strict mypy and two checkpoint shards, then verifies the complete test-file union. The PR check appears as `nonexp-sudoku-pr-checkpoint (project-6b810532-a302-48dc-b56)` on GitHub. The GitHub-hosted checkpoint workflow was retired after an exact-head Cloud Build PR succeeded.

At cutover, `main` had no branch protection and GitHub's rules API reported that rulesets were unavailable for the current private-repository plan. The Cloud Build check is visible but is not a required merge gate. If branch protection becomes available, configure this observed check as required and verify the rule on a separate PR.

## Other verification

`cloudbuild.native.yaml` supplies native and independent-oracle integration verification; `cloudbuild.research.yaml` supplies explicitly selected research and benchmark suites. These recipes have not been activated as scheduled or release triggers in this cutover. Existing specialized GitHub workflows remain available, including the manual upstream Lean source trace. Avoid assuming they ran merely because the routine checkpoint passed.

Cloud Build source admission fails closed if the provider supplies no `.git` directory or if the provider revision and checked-out commit disagree. Without a trusted base SHA, the checkpoint selects all tests. Shards run sequentially because build steps share `/workspace`.

Build logs contain the exact source revision and SHA-256 digests of JUnit/JSON evidence. Raw evidence is not yet persisted to a separately provisioned, generation-pinned GCS bucket. The 30-second test-execution target excludes scheduling, image downloads and dependency installation.

See [Google's Cloud Build GitHub documentation](https://docs.cloud.google.com/build/docs/automating-builds/github/build-repos-from-github) for trigger configuration.

## Independent Rust port lane

Rust ETH port work under `rust/lean_eth_reference/` can be tested without
running the Python/Cython checkpoint, Lean build, or research benchmarks.

- `.github/workflows/rust.yml` runs **only** for PRs/pushes touching
  the Rust crate, plus explicit manual dispatch. It uses
  Rust **1.99.1** and checks formatting, locked offline tests, and strict
  Clippy. It has no Python installation, job dependency, or shared artifact.
  It can be manually dispatched against the Rust PR branch before the crate
  reaches `main`. GitHub Actions runner minutes still apply.
- `cloudbuild.rust.yaml` is an **alternative** independent managed runner
  recipe with exact Git HEAD admission and the same three Rust checks.
  `config/cloudbuild-rust-pr-trigger.json` describes an automatic
  Rust-only Cloud Build PR trigger. Activate it only if using the managed
  lane in place of the GitHub Actions auto lane; otherwise every Rust PR
  would pay for both providers. Do not silently enable both.
- `config/cloudbuild-pr-checkpoint-trigger.json` and
  `config/cloudbuild-main-checkpoint-trigger.json` describe the **desired
  changes** to the two existing Python checkpoint triggers. The
  `ignoredFiles` list skips a checkpoint when **every** changed path
  belongs to the self-contained Rust crate or its CI files. Mixed Rust and
  Python changes still run the Python checkpoint.

**Important operational boundary:** JSON in Git does not update live Cloud
Build triggers. An authorized GCP operator must inspect the existing trigger
IDs and service accounts, compare them with these manifests, then update the
two existing checkpoint triggers with their `ignoredFiles` field. Confirm
the live readback before asserting that Rust-only PRs no longer trigger
Python Cloud Build. The Rust Cloud Build PR trigger is optional; do not
create it merely to duplicate the GitHub Actions Rust workflow. Reuse the
existing repository connection and dedicated `nonexp-sudoku-pr-ci` identity,
subject to a permission check; do not add a broader service account.

Acceptance: (1) Rust-only PR starts Rust CI and **does not** start Python
Cloud Build once the live filter is applied; (2) Python-only PR runs its
normal checkpoint and skips Rust; (3) mixed PR runs both; (4) manual
full verification remains available through the existing workflows/recipes.
Rust tests are not a substitute for source-executed Lean/Rust differential
conformance, which remains a separately gated verification obligation.
