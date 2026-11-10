# Cloud Build PR trigger activation (2026-11-10)

The `nonexp-sudoku` repository is linked to the existing `engineering-infra-native-ci` Cloud Build connection in `project-6b810532-a302-48dc-b56`, region `us-west1`.

The `nonexp-sudoku-pr-checkpoint` trigger targets pull requests to `main` and uses `cloudbuild.yaml`. Owner and collaborator PRs run automatically; outside contributors require `/gcbrun`. The trigger does not require per-build Google approval. Its dedicated `nonexp-sudoku-pr-ci` service account has project log-writing permission, rather than using an existing shared-bucket reader.

Do not remove the existing required GitHub Actions checkpoint until a real exact-head PR build, its GitHub status, and branch-protection parity have been verified. The existing Cloud Build recipes do not persist raw evidence to a dedicated bucket.
