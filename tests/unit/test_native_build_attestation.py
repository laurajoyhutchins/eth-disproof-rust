"""Build evidence must fail closed when source or binary identity changes."""
from __future__ import annotations

import json
from pathlib import Path
import pytest
from scripts.evidence import validate_attestation

pytestmark = pytest.mark.checkpoint


def test_native_build_manifest_requires_exact_sources_and_binaries(tmp_path: Path) -> None:
    hashes = {"source_sha256": "a" * 64}
    binaries = {k: {"importable": True, "filename": k + ".so",
                     "binary_sha256": chr(98 + i) * 64}
                for i, k in enumerate(("native_ring", "native_sparse", "native_recursive"))}
    assert not validate_attestation(tmp_path, hashes, binaries)["valid"]
    out = tmp_path / "artifacts" / "native-build.json"
    out.parent.mkdir()
    record = {"schema_version": 1, "build_succeeded": True,
              "source_inputs_stable": True, "source_sha256": hashes["source_sha256"],
              "binaries": binaries}
    out.write_text(json.dumps(record))
    assert validate_attestation(tmp_path, hashes, binaries)["valid"]
    assert not validate_attestation(tmp_path, {"source_sha256": "0" * 64}, binaries)["valid"]
    changed = {**binaries, "native_ring": {**binaries["native_ring"],
                                        "binary_sha256": "f" * 64}}
    assert not validate_attestation(tmp_path, hashes, changed)["valid"]
    record["source_inputs_stable"] = False
    out.write_text(json.dumps(record))
    assert not validate_attestation(tmp_path, hashes, binaries)["valid"]
    out.write_text("not json")
    assert not validate_attestation(tmp_path, hashes, binaries)["valid"]
