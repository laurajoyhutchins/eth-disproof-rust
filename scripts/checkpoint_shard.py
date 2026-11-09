"""Pytest collection adapter for conservative checkpoint sharding."""
from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.shard_contract import SCHEMA_VERSION, owned_nodeids

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
