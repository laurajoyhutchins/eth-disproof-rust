# Cloud Build checkpoint activation (2026-11-10)

The `nonexp-sudoku` repository is linked to the existing `engineering-infra-native-ci` Cloud Build connection in `project-6b810532-a302-48dc-b56`, region `us-west1`.

The `nonexp-sudoku-pr-checkpoint` trigger runs `cloudbuild.yaml` for pull requests to `main`. Owner and collaborator PRs run automatically; outside contributors require `/gcbrun`. The `nonexp-sudoku-main-checkpoint` trigger runs the same recipe on pushes to `main`. Both use the dedicated `nonexp-sudoku-pr-ci` service account, which has project log-writing permission rather than access to a shared CI bucket.

A real PR build passed on its exact head and reported a successful GitHub check. The redundant GitHub Actions `Checkpoint` workflow was disabled after this verification. Other manual and specialized workflows have not been migrated by this cutover.

As inspected during activation, `main` has no branch protection and GitHub's repository rules API reports that the current private-repository plan does not support rulesets. A green Cloud Build check is therefore not a merge requirement. Configure a required Cloud Build check when the account supports branch protection. The Cloud Build recipes do not yet persist raw evidence to a dedicated bucket.
