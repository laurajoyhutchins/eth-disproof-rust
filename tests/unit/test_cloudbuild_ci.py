"""Remote CI must attest exact source and preserve the two-shard union."""
from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts import cloudbuild_ci


@pytest.mark.checkpoint
def test_cloudbuild_requires_full_trigger_sha() -> None:
    with pytest.raises(ValueError, match="full commit SHA"):
        cloudbuild_ci.require_checkout("local")


@pytest.mark.checkpoint
def test_cloudbuild_refuses_mismatched_checkout(monkeypatch: pytest.MonkeyPatch) -> None:
    def fake_run(*args: object, **kwargs: object) -> SimpleNamespace:
        return SimpleNamespace(stdout="a" * 40 + "\n")

    monkeypatch.setattr(cloudbuild_ci.subprocess, "run", fake_run)
    with pytest.raises(ValueError, match="differs from trigger"):
        cloudbuild_ci.require_checkout("b" * 40)


@pytest.mark.checkpoint
def test_cloudbuild_keeps_aggregate_and_strict_typing() -> None:
    root = Path(__file__).resolve().parents[2]
    config = (root / "cloudbuild.yaml").read_text()
    assert "scripts.cloudbuild_ci checkpoint" in config
    assert "mypy --strict --no-incremental" in config
    assert "artifacts/shards/**/*" in config
    source = (root / "scripts/cloudbuild_ci.py").read_text()
    assert '"--shard-count", "2"' in source
    assert '"-m", "scripts.aggregate_checkpoint"' in source


@pytest.mark.checkpoint
def test_cloudbuild_has_no_github_actions_runner_dependency() -> None:
    root = Path(__file__).resolve().parents[2]
    for config in ("cloudbuild.yaml", "cloudbuild-native.yaml"):
        source = (root / config).read_text()
        assert "runs-on:" not in source
        assert "github.event" not in source
        assert "CLOUD_LOGGING_ONLY" in source
