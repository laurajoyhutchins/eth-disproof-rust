"""Pure exact partition contracts for independently executed pytest shards."""
from __future__ import annotations

from hashlib import sha256
from typing import Sequence

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


