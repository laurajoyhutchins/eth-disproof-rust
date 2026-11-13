"""Create a standalone Cargo test crate, even under an enclosing repository workspace.

Lean acceptance checks keep temporary sources inside the pinned Lake root.
When that root itself is inside a Cargo workspace, a generated crate MUST declare
its own workspace; otherwise Cargo refuses it before any differential executes.
"""
from __future__ import annotations

import json
from pathlib import Path
import re


def isolated_cargo_manifest(name: str, rust_crate: Path) -> str:
    """A closed, parser-safe Cargo manifest for an independently built test crate."""
    if re.fullmatch(r"[a-zA-Z][a-zA-Z0-9_-]*", name) is None:
        raise ValueError("invalid generated Cargo package name")
    return (
        "[package]\n"
        f"name = {json.dumps(name)}\n"
        'version = "0.0.0"\n'
        'edition = "2024"\n'
        "\n"
        "[workspace]\n"
        "\n"
        "[dependencies]\n"
        "lean_eth_reference = { package = \"lean-eth-reference\", path = "
        + json.dumps(str(rust_crate.resolve())) + " }\n"
    )
