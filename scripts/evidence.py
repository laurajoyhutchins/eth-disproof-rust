"""Stable source and verification manifests shared by local evidence producers.

Hashes identify source *bytes* and relative paths, not merely a Git revision:
tracked but uncommitted edits therefore change the fingerprint. The binary
manifest separately identifies compiled native artifacts actually importable
in the current interpreter. A source fingerprint does not attest the binary
was built from that source.
"""
from __future__ import annotations

import json
from hashlib import sha256
from importlib import import_module
from pathlib import Path
import subprocess
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
SOURCE_EXTENSIONS = frozenset({".py", ".pyx", ".pxd", ".pyi"})
VERIFY_EXTENSIONS = frozenset({".py", ".json", ".yml", ".yaml", ".toml"})
NATIVE_MODULES = ("native_ring", "native_sparse", "native_recursive")


def _files(directory: Path, suffixes: frozenset[str]) -> set[Path]:
    return {p for p in directory.rglob("*") if p.is_file() and p.suffix in suffixes}


def source_files(root: Path = ROOT) -> list[Path]:
    """All maintained runtime, Cython interface and packaging input files."""
    result = _files(root / "src", SOURCE_EXTENSIONS)
    result.update(p for p in root.iterdir() if p.is_file() and p.suffix in SOURCE_EXTENSIONS)
    for filename in ("pyproject.toml", "setup.py", "build_native.py", "MANIFEST.in"):
        path = root / filename
        if path.is_file():
            result.add(path)
    return sorted(result)


def verification_files(root: Path = ROOT) -> list[Path]:
    """Scripts, reference algorithms, test cases/fixtures and CI settings."""
    result: set[Path] = set()
    for dirname in ("tests", "reference", "research", "benchmarks", "scripts", ".github/workflows"):
        path = root / dirname
        if path.is_dir():
            result.update(_files(path, VERIFY_EXTENSIONS))
    return sorted(result)


def hash_files(paths: Iterable[Path], root: Path = ROOT) -> str:
    digest = sha256()
    for path in sorted(paths):
        data = path.read_bytes()
        digest.update(path.relative_to(root).as_posix().encode("utf-8") + b"\0")
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def fingerprints(root: Path = ROOT) -> dict[str, str]:
    return {
        "source_sha256": hash_files(source_files(root), root),
        "verification_sources_sha256": hash_files(verification_files(root), root),
    }


def git_provenance(root: Path = ROOT) -> dict[str, str | bool | None]:
    try:
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                                text=True, capture_output=True, timeout=5, check=False)
        if commit.returncode != 0:
            return {"revision": None, "dirty": None}
        status = subprocess.run(["git", "status", "--porcelain", "--untracked-files=normal"],
                                cwd=root, text=True, capture_output=True, timeout=5,
                                check=False)
        return {"revision": commit.stdout.strip(),
                "dirty": bool(status.stdout.strip()) if status.returncode == 0 else None}
    except (OSError, subprocess.TimeoutExpired):
        return {"revision": None, "dirty": None}


def native_binaries() -> dict[str, dict[str, str | bool | None]]:
    """Hash the exact binaries found by the current interpreter, if present."""
    result: dict[str, dict[str, str | bool | None]] = {}
    for name in NATIVE_MODULES:
        try:
            module = import_module(name)
            origin = getattr(module, "__file__", None)
            path = Path(origin) if isinstance(origin, str) else None
        except (ImportError, OSError):
            path = None
        binary = path if path and path.is_file() and path.suffix in (".so", ".pyd") else None
        result[name] = {
            "importable": bool(binary),
            "filename": binary.name if binary else None,
            "binary_sha256": sha256(binary.read_bytes()).hexdigest() if binary else None,
        }
    return result


def validate_attestation(
    root: Path, source_fingerprints: dict[str, str],
    binaries: dict[str, dict[str, str | bool | None]],
) -> dict[str, Any]:
    path = root / "artifacts" / "native-build.json"
    if not path.is_file():
        return {"valid": False, "reason": "no local native build manifest"}
    try:
        data = json.loads(path.read_text())
    except (ValueError, OSError) as exc:
        return {"valid": False, "reason": f"unreadable build manifest: {exc}"}
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        return {"valid": False, "reason": "invalid build manifest schema"}
    if not data.get("build_succeeded") or not data.get("source_inputs_stable"):
        return {"valid": False, "reason": "build did not record stable successful inputs"}
    if data.get("source_sha256") != source_fingerprints["source_sha256"]:
        return {"valid": False, "reason": "native build source fingerprint is stale"}
    built = data.get("binaries")
    if not isinstance(built, dict) or set(built) != set(NATIVE_MODULES):
        return {"valid": False, "reason": "incomplete build binary manifest"}
    for name in NATIVE_MODULES:
        expected = built[name]
        actual = binaries.get(name)
        if not isinstance(expected, dict) or actual is None:
            return {"valid": False, "reason": f"missing {name} binary"}
        if (not actual.get("importable") or
                expected.get("binary_sha256") != actual.get("binary_sha256") or
                expected.get("filename") != actual.get("filename")):
            return {"valid": False, "reason": f"{name} binary hash or filename mismatch"}
    return {"valid": True, "reason": "source inputs and loaded binaries match build manifest",
            "manifest": "artifacts/native-build.json"}
