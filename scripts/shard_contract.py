"""Pure file-ownership policy for complete independent checkpoint shards.

Partitioning files, rather than collected test IDs, also owns pytest's
collection-time skips (e.g. importorskip) exactly once.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
from typing import Sequence

SCHEMA_VERSION = 2


def checkpoint_files(root: Path) -> list[str]:
    tests = root / "tests"
    if not tests.is_dir():
        raise ValueError("missing checkpoint test root")
    result = sorted({
        p.relative_to(root).as_posix()
        for p in tests.rglob("*.py") if p.is_file()
        and (p.name.startswith("test_") or p.name.endswith("_test.py"))
    })
    if not result:
        raise ValueError("no checkpoint test files found")
    return result


def shard_for(path: str, count: int) -> int:
    if type(count) is not int or count < 1:
        raise ValueError("positive shard count required")
    return int.from_bytes(sha256(path.encode("utf-8")).digest()[:8], "big") % count


def owned_files(paths: Sequence[str], index: int, count: int) -> list[str]:
    if type(index) is not int or index < 0 or index >= count:
        raise ValueError("invalid shard index")
    return sorted(path for path in paths if shard_for(path, count) == index)


def verify_partition(manifests: Sequence[dict[str, object]]) -> list[str]:
    if not manifests:
        raise ValueError("missing shards")
    count = manifests[0].get("shard_count")
    if type(count) is not int or count < 2 or len(manifests) != count:
        raise ValueError("incomplete shard set")
    full = manifests[0].get("all_test_files")
    if not isinstance(full, list) or not full or any(not isinstance(x, str) for x in full):
        raise ValueError("invalid complete checkpoint file inventory")
    if full != sorted(set(full)):
        raise ValueError("duplicate or unordered checkpoint test files")
    union: set[str] = set()
    indices: set[int] = set()
    for manifest in manifests:
        index = manifest.get("shard_index")
        if (manifest.get("schema_version") != SCHEMA_VERSION
                or type(index) is not int or index in indices
                or index < 0 or index >= count
                or manifest.get("shard_count") != count
                or manifest.get("all_test_files") != full):
            raise ValueError("inconsistent checkpoint shard manifest")
        selected = manifest.get("selected_test_files")
        if selected != owned_files(full, index, count):
            raise ValueError("incorrect checkpoint file assignment")
        if not isinstance(selected, list) or any(x in union for x in selected):
            raise ValueError("overlapping checkpoint files")
        indices.add(index)
        union.update(selected)
    if indices != set(range(count)) or union != set(full):
        raise ValueError("missing checkpoint test files or shards")
    return full
