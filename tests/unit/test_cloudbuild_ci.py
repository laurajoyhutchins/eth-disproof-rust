"""Fail closed on accidental dilution of the staged Cloud Build verification."""
import json
from pathlib import Path
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[2]


def _config(filename: str) -> str:
    return (ROOT / filename).read_text(encoding="utf-8")


@pytest.mark.checkpoint
def test_checkpoint_requires_exact_source_two_shards_and_complete_aggregate() -> None:
    config = _config("cloudbuild.yaml")
    assert "'$COMMIT_SHA'" in config and "'$REVISION_ID'" in config
    assert 'test -d .git' in config and 'git rev-parse --verify HEAD' in config
    assert 'id: plan' in config and 'scripts/change_impact.py --output' in config
    for shard in (0, 1):
        assert f'id: shard-{shard}' in config
        assert f'--shard-count 2 --shard-index {shard}' in config
        assert f'artifacts/shards/checkpoint-shard-{shard}' in config
    # Separate shard reports do not imply filesystem isolation in Cloud Build.
    assert "waitFor: ['shard-0']" in config
    assert "waitFor: ['shard-0', 'shard-1']" in config
    assert 'scripts.aggregate_checkpoint --root artifacts/shards' in config
    assert '--head "$$expected" --count 2' in config
    assert 'python -m mypy --strict --no-incremental' in config
    assert 'CLOUD_LOGGING_ONLY' in config
    assert 'test "$$expected" = "$$revision"' in config


@pytest.mark.checkpoint
def test_native_cloudbuild_preserves_independent_oracles() -> None:
    config = _config("cloudbuild.native.yaml")
    assert 'git rev-parse HEAD' in config
    assert 'python build_native.py' in config
    assert '--require-native --require-native-attestation' in config
    assert '--require-backend flint --require-backend ganak' in config
    assert 'scripts/verify.py integration' in config
    assert 'scripts/verify.py extended' in config


@pytest.mark.checkpoint
def test_research_cloudbuild_does_not_run_as_required_checkpoint() -> None:
    config = _config("cloudbuild.research.yaml")
    assert "_SUITE: cnf-scaling" in config
    assert "bash scripts/cloudbuild_research.sh '$_SUITE'" in config
    assert 'CLOUD_LOGGING_ONLY' in config
    assert 'git rev-parse HEAD' in config


@pytest.mark.checkpoint
def test_research_suite_script_refuses_unknown_names() -> None:
    script = ROOT / 'scripts' / 'cloudbuild_research.sh'
    assert subprocess.run(['bash', '-n', str(script)], check=False).returncode == 0
    for name in ('', 'lean-source-trace', 'checkpoint', '$(exit 0)', 'native-cutover; true'):
        result = subprocess.run(
            ['bash', str(script), name], cwd=ROOT, capture_output=True,
            text=True, check=False,
        )
        assert result.returncode == 2
        assert 'unknown research suite' in result.stderr


@pytest.mark.checkpoint
def test_automatic_cloud_build_trigger_admits_owners_without_per_run_approval() -> None:
    trigger = json.loads(_config("config/cloudbuild-pr-checkpoint-trigger.json"))
    expected_repo = (
        "projects/project-6b810532-a302-48dc-b56/locations/us-west1/"
        "connections/engineering-infra-native-ci/repositories/nonexp-sudoku"
    )
    assert trigger["name"] == "nonexp-sudoku-pr-checkpoint"
    assert trigger["filename"] == "cloudbuild.yaml"
    assert trigger["repositoryEventConfig"] == {
        "repository": expected_repo,
        "pullRequest": {
            "branch": "^main$",
            "commentControl": "COMMENTS_ENABLED_FOR_EXTERNAL_CONTRIBUTORS_ONLY",
        },
    }
    assert trigger["approvalConfig"] == {"approvalRequired": False}
    assert trigger["serviceAccount"] == (
        "projects/project-6b810532-a302-48dc-b56/serviceAccounts/"
        "engineering-infra-native-ci@project-6b810532-a302-48dc-b56.iam.gserviceaccount.com"
    )
    # No arbitrary build, push, webhook, deployment, custom worker or
    # implicit opt-out from the tested checkpoint command is permitted.
    assert set(trigger) == {
        "name", "description", "filename", "serviceAccount",
        "approvalConfig", "repositoryEventConfig",
    }
    assert "jobs:" not in _config("cloudbuild.yaml")
    assert "python scripts/verify.py checkpoint" in _config("cloudbuild.yaml")
    assert "--shard-count 2 --shard-index 0" in _config("cloudbuild.yaml")
    assert "--shard-count 2 --shard-index 1" in _config("cloudbuild.yaml")
    assert "scripts.aggregate_checkpoint" in _config("cloudbuild.yaml")


@pytest.mark.checkpoint
def test_cloud_build_setup_requires_proven_parity_before_retiring_github_gate() -> None:
    doc = _config("docs/cloud-build-ci.md")
    assert "No per-build owner approvals" in doc
    assert "--trigger-config=config/cloudbuild-pr-checkpoint-trigger.json" in doc
    assert "A second normal PR update should" in doc
    assert "Only after an exact-head successful PR" in doc
    assert "Then disable the redundant GitHub-hosted checkpoint" in " ".join(doc.split())
