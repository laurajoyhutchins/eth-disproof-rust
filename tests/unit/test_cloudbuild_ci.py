"""Fail closed on accidental dilution of the staged Cloud Build verification."""
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
def test_rust_ci_has_no_python_or_lean_dependency() -> None:
    """The standalone Rust lane must not silently fan out to solver CI."""
    rust = _config(".github/workflows/rust.yml")
    managed = _config("cloudbuild.rust.yaml")
    for command in (
        "cargo fmt --all -- --check",
        "cargo test --locked --offline --all-targets",
        "cargo clippy --locked --offline --all-targets -- -D warnings",
    ):
        assert command in rust
        assert command in managed
    assert "rust/lean_eth_reference" in rust
    assert "rust/lean_eth_reference" in managed
    assert "1.99.1" in rust and "rust:1.99.1-bookworm" in managed
    assert "  workflow_dispatch:" in rust
    assert "  pull_request:" not in rust and "  push:" not in rust
    for unwanted in ("setup-python", "pip install", "mypy", "lake build", "scripts/verify.py"):
        assert unwanted not in rust
        assert unwanted not in managed


@pytest.mark.checkpoint
def test_cloudbuild_trigger_files_isolate_rust_only_changes() -> None:
    import json

    rust = json.loads(_config("config/cloudbuild-rust-pr-trigger.json"))
    pr = json.loads(_config("config/cloudbuild-pr-checkpoint-trigger.json"))
    main = json.loads(_config("config/cloudbuild-main-checkpoint-trigger.json"))
    assert "filename" not in rust and rust["build"]["steps"][1]["id"] == "rust-port"
    assert rust["includedFiles"] == ["rust/lean_eth_reference/**"]
    ignored = [
        "rust/lean_eth_reference/**",
        ".github/workflows/rust.yml",
        "cloudbuild.rust.yaml",
        "config/cloudbuild-rust-pr-trigger.json",
    ]
    assert pr["ignoredFiles"] == ignored
    assert main["ignoredFiles"] == ignored
    assert pr["filename"] == main["filename"] == "cloudbuild.yaml"
    assert pr["repositoryEventConfig"]["pullRequest"]["branch"] == "^main$"
    assert main["repositoryEventConfig"]["push"]["branch"] == "^main$"
    for item in (rust, pr, main):
        assert item["approvalConfig"] == {"approvalRequired": False}
        assert "nonexp-sudoku-pr-ci@" in item["serviceAccount"]
