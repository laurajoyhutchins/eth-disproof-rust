"""Deterministic, auditable partition of the *whole* checkpoint collection.

Runs in separate GitHub runner VMs; never within same-runner xdist workers.
The aggregate verifier checks the exact union of collected test identities.
"""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
from typing import Sequence

import pytest

SCHEMA_VERSION = 1


def shard_for(nodeid: str, count: int) -> int:
    if type(count) is not int or count < 1:
        raise ValueError("positive shard count required")
    return int.from_bytes(sha256(nodeid.encode("utf-8")).digest()[:8], "big") % count


def owned_nodeids(nodeids: Sequence[str], index: int, count: int) -> list[str]:
    if type(index) is not int or index < 0 or index >= count:
        raise ValueError("invalid shard index")
    return sorted(nodeid for nodeid in nodeids if shard_for(nodeid, count) == index)


def verify_partition(manifests: Sequence[dict[str, object]]) -> list[str]:
    if not manifests:
        raise ValueError("missing shards")
    count = manifests[0].get("shard_count")
    if type(count) is not int or count < 2 or len(manifests) != count:
        raise ValueError("incomplete shard set")
    full = manifests[0].get("all_nodeids")
    if not isinstance(full, list) or not full or any(not isinstance(x, str) for x in full):
        raise ValueError("invalid full checkpoint test identities")
    if full != sorted(set(full)):
        raise ValueError("duplicate or unordered full test identities")
    union: set[str] = set()
    indices: set[int] = set()
    for manifest in manifests:
        index = manifest.get("shard_index")
        if (manifest.get("schema_version") != SCHEMA_VERSION
                or type(index) is not int or index in indices
                or index < 0 or index >= count
                or manifest.get("shard_count") != count
                or manifest.get("all_nodeids") != full):
            raise ValueError("inconsistent checkpoint shard manifest")
        selected = manifest.get("selected_nodeids")
        if selected != owned_nodeids(full, index, count):
            raise ValueError("incorrect checkpoint shard assignment")
        if not isinstance(selected, list) or any(x in union for x in selected):
            raise ValueError("overlapping checkpoint test identities")
        indices.add(index)
        union.update(selected)
    if indices != set(range(count)) or union != set(full):
        raise ValueError("missing checkpoint tests or shards")
    return full


def pytest_addoption(parser: pytest.Parser) -> None:
    group = parser.getgroup("checkpoint-sharding")
    group.addoption("--checkpoint-shard-index", type=int, default=0)
    group.addoption("--checkpoint-shard-count", type=int, default=1)
    group.addoption("--checkpoint-shard-manifest", type=str, default=None)


@pytest.hookimpl(trylast=True)
def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    count = config.getoption("checkpoint_shard_count")
    if count == 1:
        return
    index = config.getoption("checkpoint_shard_index")
    output = config.getoption("checkpoint_shard_manifest")
    if (type(index) is not int or type(count) is not int
            or index < 0 or count < 2 or index >= count or not output):
        raise pytest.UsageError("invalid checkpoint sharding configuration")
    all_nodes = sorted(
        item.nodeid for item in items
        if item.get_closest_marker("checkpoint") is not None
    )
    if not all_nodes or len(all_nodes) != len(set(all_nodes)):
        raise pytest.UsageError("missing or duplicated full checkpoint collection")
    selected = owned_nodeids(all_nodes, index, count)
    selected_set = set(selected)
    deselected = [
        item for item in items
        if item.get_closest_marker("checkpoint") is not None
        and item.nodeid not in selected_set
    ]
    if deselected:
        config.hook.pytest_deselected(items=deselected)
        deselected_ids = {id(item) for item in deselected}
        items[:] = [item for item in items if id(item) not in deselected_ids]
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "shard_index": index, "shard_count": count,
        "all_nodeids": all_nodes, "selected_nodeids": selected,
    }
    path = Path(output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, indent=2) + "\n")
