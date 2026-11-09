# Sudoku verification: agent-local feedback and Cloud Build CI

The 30-second checkpoint is **agent-local**, not a GitHub Actions service-level
objective. Agents run fast local verification after edits. Cloud Build owns
remote PR/main checks and resource-intensive native verification. GitHub is
the source of truth for revisions, PRs and published check results.

## Verification contracts

- Local: `python scripts/verify.py checkpoint` (the 30-second feedback target
  is informational, never permission to omit tests). Run strict mypy locally
  when typing or maintained interfaces change.
- Remote PR/main: `cloudbuild.yaml`. The trigger supplies an exact commit
  SHA. Full checkpoint runs in two independent Python processes, then
  `scripts.aggregate_checkpoint` requires matching source fingerprints,
  complete test ownership and zero failures. Strict mypy runs before it.
  No PR diff base is inferred from the shallow Cloud Build checkout, so
  change-impact selection conservatively chooses the **full** suite.
- Remote release/manual: `cloudbuild-native.yaml`. Build attested Cython
  extensions, require FLINT and Ganak backends and execute integration and
  extended verification. Backend absence fails instead of silently skipping.
- The other research-specific scaling and benchmark workflows remain manual
  until individually moved to Cloud Build. Their results are **experiments**,
  not proof of non-exponential worst-case complexity.
- A successful remote build archives raw JSON/JUnit and native attestation
  under the Cloud Build ID in the GCS evidence bucket. Cloud Build itself
  retains failure logs; built-in GCS artifact upload requires build success.

## One-time GCP wiring

Project: `project-6b810532-a302-48dc-b56`. Region: `us-west1`.
This is **not** provisioned merely by merging the repository files.
The private GitHub repository must first be connected as a **second-generation
Cloud Build repository** (GitHub authorization happens through the Google
Cloud Console). The connector cannot create that external connection.

Use a least-privilege build identity with no access to source corpora,
deployment credentials, infrastructure administration or Secret Manager.
In an appropriately authorized GCP shell:

```bash
PROJECT=project-6b810532-a302-48dc-b56
REGION=us-west1
BUCKET="gs://${PROJECT}-sudoku-ci"
ACCOUNT="nonexp-sudoku-ci@${PROJECT}.iam.gserviceaccount.com"

gcloud iam service-accounts create nonexp-sudoku-ci --project "$PROJECT" \
  --display-name="Sudoku untrusted CI"
gcloud projects add-iam-policy-binding "$PROJECT" \
  --member="serviceAccount:$ACCOUNT" --role=roles/logging.logWriter
gcloud storage buckets create "$BUCKET" --project "$PROJECT" \
  --location "$REGION" --uniform-bucket-level-access
gcloud storage buckets add-iam-policy-binding "$BUCKET" \
  --member="serviceAccount:$ACCOUNT" --role=roles/storage.objectCreator
```

Grant the **Cloud Build service agent** any documented repository-connection
permissions separately. The trigger creator also needs permission to use
the service account. Do not grant project editor or blanket storage admin
to the runtime identity.

After connecting `laurajoyhutchins/nonexp-sudoku`, copy its exact 2nd-gen
repository resource name from the Cloud Build Repositories page. For example,
`projects/$PROJECT/locations/$REGION/connections/CONNECTION/repositories/REPO`.
Use that resource as `REPOSITORY` below:

```bash
SERVICE_ACCOUNT="projects/$PROJECT/serviceAccounts/$ACCOUNT"

gcloud builds triggers create github \
  --project="$PROJECT" --region="$REGION" \
  --name=sudoku-pr-checkpoint --repository="$REPOSITORY" \
  --pull-request-pattern='^main$' \
  --comment-control=COMMENTS_ENABLED_FOR_EXTERNAL_CONTRIBUTORS_ONLY \
  --build-config=cloudbuild.yaml \
  --service-account="$SERVICE_ACCOUNT"

gcloud builds triggers create github \
  --project="$PROJECT" --region="$REGION" \
  --name=sudoku-main-checkpoint --repository="$REPOSITORY" \
  --branch-pattern='^main$' --build-config=cloudbuild.yaml \
  --service-account="$SERVICE_ACCOUNT"

gcloud builds triggers create github \
  --project="$PROJECT" --region="$REGION" \
  --name=sudoku-native-release --repository="$REPOSITORY" \
  --tag-pattern='^v.*$' --build-config=cloudbuild-native.yaml \
  --service-account="$SERVICE_ACCOUNT"
```

No GitHub Actions dispatcher is involved. Cloud Build's GitHub integration
publishes the trigger status on the PR/commit; check the actual reported check
name before editing branch rules. Do not enable the `include-logs-with-status`
option without reviewing the additional permission and exposure implications.

## Cutover gate (do not skip)

1. Run the new PR trigger on a real exact-head revision. Verify the SHA check,
   mypy, both shard JSON/JUnit reports, complete aggregate and GCS evidence.
   Exercise a failing test and confirm the GitHub check is red.
2. Exercise a successful native Cloud Build run with the independent oracles.
   If it fails on package acquisition, fix the image/dependencies without
   dropping backend requirements.
3. Confirm GitHub displays the Cloud Build trigger status, then update any
   required `checkpoint` branch rule to require `sudoku-pr-checkpoint`.
   Private-repository branch protections could not be read by the GitHub
   connector, so this is a deliberate manual verification.
4. Only after those receipts, remove the automatic triggers and scheduled jobs
   in `.github/workflows/` and retire the draft GCP **Actions-runner** migration
   PR #84. Keep any manual-only formal verification workflow manual.
   Do not disable existing required checks before status parity is proven.

### Limitations

The current GitHub connector can edit this repository but cannot administer
Google Cloud Build, install the GitHub Cloud Build app, provision GCP IAM or
read private branch-protection settings. These steps need an authorized GCP
identity and a live build receipt. No successful Cloud Build run is asserted
by the presence of these files.
