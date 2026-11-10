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
