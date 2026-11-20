"""Audit deep-proof workflow selectors against their actual local dependencies.

GitHub decides whether a path-filtered workflow exists before jobs start.
This offline audit runs in the unconditional Rust PR workflow. It refuses
missing source selectors but never treats a skipped or selected job as proof
acceptance. It intentionally recognizes only the simple literal selectors
used by these workflows; unsupported syntax must not silently match.
"""
from __future__ import annotations

from fnmatch import fnmatchcase
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
LEAN_JOBS = ("lean-source-refinement.yml", "lean-independent-formulations.yml")
PYTHON_JOBS = ("lean-source-refinement.yml", "original-source-graph.yml")
PINNED_ENV = (
    "instrumentation/lean-env/lean-toolchain",
    "instrumentation/lean-env/lakefile.lean",
    "instrumentation/lean-env/lake-manifest.json",
)


def pull_request_paths(workflow: str) -> tuple[str, ...]:
    """Read only the top-level pull_request.paths list, not shell snippets."""
    lines = workflow.splitlines()
    if lines.count("  pull_request:") != 1:
        raise ValueError("expected one path-filtered pull_request event")
    start = lines.index("  pull_request:") + 1
    event = []
    for line in lines[start:]:
        if line and not line.startswith("  ") and not line.lstrip().startswith("#"):
            break
        if re.match(r"^  [a-zA-Z_-]+:", line):
            break
        event.append(line)
    if event.count("    paths:") != 1:
        raise ValueError("expected a literal pull_request.paths list")
    result: list[str] = []
    for line in event[event.index("    paths:") + 1:]:
        if line.strip() == "" or line.lstrip().startswith("#"):
            continue
        match = re.fullmatch(r"""      - (['"])([^'"]+)\1(?:\s+#.*)?""", line)
        if not match:
            raise ValueError(f"nonliteral or unsupported paths selector: {line}")
        pattern = match.group(2)
        if pattern.startswith("!") or any(c in pattern for c in "?[]{}"):
            raise ValueError(f"unsupported GitHub path selector: {pattern}")
        result.append(pattern)
    if not result or len(set(result)) != len(result):
        raise ValueError("empty or duplicate paths selector")
    return tuple(result)


def covered(path: str, patterns: tuple[str, ...]) -> bool:
    """Match the supported exact, segment-wildcard, and recursive-directory forms.

    Unlike fnmatchcase on the entire path, a single '*' cannot swallow '/'.
    """
    for pattern in patterns:
        if pattern.endswith("/**") and pattern.count("**") == 1:
            if path.startswith(pattern[:-3] + "/"):
                return True
            continue
        if "**" in pattern:
            raise ValueError(f"unsupported recursive glob: {pattern}")
        parts = path.split("/")
        globs = pattern.split("/")
        if len(parts) == len(globs) and all(
            fnmatchcase(part, part_glob) for part, part_glob in zip(parts, globs)
        ):
            return True
    return False


def _lean_imports(path: Path) -> set[str]:
    imports = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*import\s+(.+)$", line)
        if match:
            imports.update(name for name in match.group(1).split() if name.startswith("ACC."))
    return imports


def lean_inputs(root: Path, workflow: str) -> set[str]:
    """Track emitted Lean proof roots and transitive, locally authored ACC imports."""
    proofs = set()
    modules = set()
    for line in workflow.splitlines():
        if "lake env lean" in line:
            proofs.update(re.findall(r"eth/proofs/[A-Za-z0-9_-]+\.lean", line))
        if re.search(r"\blake\s+(?:-K\s+\S+\s+)?build\b", line):
            modules.update(re.findall(r"\bACC\.[A-Za-z_][\w.]*", line))
    if not proofs:
        raise ValueError("proof selector has no actual Lean elaboration roots")
    dependencies = set(proofs) | set(PINNED_ENV)
    pending = list(proofs)
    seen = set()
    while pending or modules:
        if modules:
            module = modules.pop()
            if not re.fullmatch(r"ACC\.[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", module):
                raise ValueError(f"invalid local Lean module: {module}")
            pending.append("instrumentation/lean-env/" + module.replace(".", "/") + ".lean")
        else:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            file = root / current
            if not file.is_file():
                raise ValueError(f"missing selected Lean dependency: {current}")
            dependencies.add(current)
            modules.update(_lean_imports(file))
    return dependencies


def _python_imports(path: Path) -> set[str]:
    modules = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^(?:from\s+([a-zA-Z_][\w.]*)\s+import|import\s+([a-zA-Z_][\w.]*))", line)
        if match:
            modules.add(match.group(1) or match.group(2))
    return modules


def python_inputs(root: Path, workflow: str) -> set[str]:
    """Follow local imports of actually executed Python tools and test fixtures."""
    scripts = set(re.findall(r"\bpython3\s+(eth/tools/[a-zA-Z_][\w-]*\.py)\b", workflow))
    for pattern in re.findall(
        r"""python3\s+-m\s+unittest\s+discover\s+-s\s+eth/tools\s+-p\s+['"]?(test_[\w*-]+\.py)""",
        workflow,
    ):
        files = list((root / "eth/tools").glob(pattern))
        if not files:
            raise ValueError(f"Python fixture pattern has no files: {pattern}")
        scripts.update("eth/tools/" + file.name for file in files)
    if not scripts:
        raise ValueError("source-data workflow has no exercised Python scripts")
    pending = list(scripts)
    seen = set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        path = root / current
        if not path.is_file():
            raise ValueError(f"missing executed Python dependency: {current}")
        for module in _python_imports(path):
            # External and standard-library imports are not repository inputs.
            if module.startswith("eth.tools."):
                candidate = "eth/tools/" + module.removeprefix("eth.tools.").replace(".", "/") + ".py"
                if not (root / candidate).is_file():
                    raise ValueError(f"missing local Python module: {module}")
            elif "." not in module:
                candidate = "eth/tools/" + module + ".py"
                if not (root / candidate).is_file():
                    continue
            else:
                continue
            pending.append(candidate)
    return seen


def verify_selection(root: Path, workflow_name: str, source: str | None = None) -> set[str]:
    path = ".github/workflows/" + workflow_name
    source = source if source is not None else (root / path).read_text(encoding="utf-8")
    patterns = pull_request_paths(source)
    required = {path}
    if workflow_name in LEAN_JOBS:
        required.update(lean_inputs(root, source))
    if workflow_name in PYTHON_JOBS:
        required.update(python_inputs(root, source))
    if workflow_name == "original-source-graph.yml":
        required.update(PINNED_ENV)
    missing = sorted(name for name in required if not covered(name, patterns))
    if missing:
        raise ValueError(f"{workflow_name} skips actual verification dependencies: {missing}")
    return required


def verify_all(root: Path = ROOT) -> None:
    for name in sorted(set(LEAN_JOBS) | set(PYTHON_JOBS)):
        verify_selection(root, name)


if __name__ == "__main__":
    verify_all()
    print("DEEP_PROOF_SELECTION=SOURCE_CLOSURE_COVERED")
