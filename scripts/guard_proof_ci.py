"""Keep heavyweight Lean/Mathlib verification outside ordinary CI.

Proof toolchains may be used in GitHub Actions only by manually dispatched
workflows. This stdlib-only guard runs before the Python checkpoint.
"""

from __future__ import annotations

import re
from pathlib import Path

PROOF_TOOL = re.compile(r"\b(?:lean|leanprover|mathlib4?|lake|elan)\b", re.IGNORECASE)
EVENT = re.compile(r"^  ([a-z][a-z0-9_-]*):")


def declared_events(source: str) -> set[str]:
    """Read top-level GitHub Actions event names, refusing ambiguous syntax."""
    lines = source.splitlines()
    headers = [(i, line) for i, line in enumerate(lines) if line.startswith("on:")]
    if len(headers) != 1:
        raise ValueError("expected exactly one top-level on: declaration")
    i, line = headers[0]
    inline = line[3:].split("#", 1)[0].strip()
    if inline:
        if inline.startswith("[") and inline.endswith("]"):
            events = {item.strip() for item in inline[1:-1].split(",")}
        elif re.fullmatch(r"[a-z][a-z0-9_-]*", inline):
            events = {inline}
        else:
            raise ValueError("unsupported inline on: declaration")
    else:
        events = set()
        for line in lines[i + 1 :]:
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            if not line[0].isspace():
                break
            match = EVENT.match(line)
            if match:
                events.add(match.group(1))
    if not events or "" in events:
        raise ValueError("no unambiguous event names")
    return events


def violations(workflow_dir: Path) -> list[str]:
    issues: list[str] = []
    paths = sorted((*workflow_dir.glob("*.yml"), *workflow_dir.glob("*.yaml")))
    if not paths:
        return [f"{workflow_dir}: no workflows found"]
    for path in paths:
        source = path.read_text(encoding="utf-8")
        if not PROOF_TOOL.search(source):
            continue
        try:
            events = declared_events(source)
        except ValueError as exc:
            issues.append(f"{path}: {exc}")
            continue
        if events != {"workflow_dispatch"}:
            issues.append(
                f"{path}: proof toolchain requires manual-only workflow_dispatch; "
                f"found {sorted(events)}"
            )
    return issues


def main() -> int:
    issues = violations(Path(".github/workflows"))
    for issue in issues:
        print(issue)
    if issues:
        return 1
    print("Proof toolchains are outside automatic CI triggers.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
