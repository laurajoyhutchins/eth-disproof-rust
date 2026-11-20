"""Validate exact-revision, scoped evidence claims without promoting tests to proofs.

Local validation pins the *current bytes* of every claim dependency. Optional
remote validation independently checks GitHub's workflow run, exact head,
successful job and the required successful step. Even a validated receipt
attests to a check, not to stronger semantics than its stated claim.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "eth/evidence/claims.json"
REPO = "laurajoyhutchins/eth-disproof-rust"
SHA = re.compile(r"[0-9a-f]{40}\Z")
IDENTITY = re.compile(r"[a-z][a-z0-9-]*\Z")
# Adding a proof tier requires independent rules; never infer it from a green job.
CLAIM_KINDS = {
    "abstract_lean_model": "all_admitted_model_states",
    "bounded_compiler_guard": "finite_fixtures",
}


class ReceiptError(ValueError):
    """A malformed or stale evidence claim must not be reported as current."""


def fields(data: object, expected: set[str], where: str) -> dict:
    if not isinstance(data, dict) or set(data) != expected:
        raise ReceiptError(f"{where}: expected exactly {sorted(expected)}")
    return data


def text_value(value: object, where: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ReceiptError(f"{where}: expected nonempty string")
    return value


def sha_value(value: object, where: str) -> str:
    if not isinstance(value, str) or SHA.fullmatch(value) is None:
        raise ReceiptError(f"{where}: expected lowercase 40-hex Git SHA")
    return value


def checked_path(root: Path, name: object) -> Path:
    name = text_value(name, "source path")
    path = PurePosixPath(name)
    if (path.is_absolute() or not path.parts or any(part in ("", ".", "..") for part in path.parts)
            or "\\" in name or name.startswith("./")):
        raise ReceiptError(f"unsafe source path: {name}")
    full = root.joinpath(*path.parts)
    if full.is_symlink() or not full.is_file() or not full.resolve().is_relative_to(root.resolve()):
        raise ReceiptError(f"missing or unsafe pinned source file: {name}")
    return full


def git_blob_sha(contents: bytes) -> str:
    # Git SHA-1 blob identity, deliberately not SHA-256 of just the body.
    prelude = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(prelude + contents).hexdigest()


def fetch_github(url: str) -> dict:
    token = os.environ.get("GITHUB_TOKEN", "")
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "eth-scoped-evidence-audit",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    try:
        with urlopen(Request(url, headers=headers), timeout=15) as response:
            return json.load(response)
    except (HTTPError, URLError, TimeoutError, ValueError) as exc:
        raise ReceiptError(f"remote receipt lookup failed: {exc}") from exc


def verify_remote(receipt: dict, pinned_files: list[dict], fetcher=fetch_github) -> None:
    run_id = receipt["run_id"]
    base = f"https://api.github.com/repos/{REPO}/actions/runs/{run_id}"
    run = fetcher(base)
    if not isinstance(run, dict) or (
        run.get("head_sha") != receipt["checked_head"]
        or run.get("path") != receipt["workflow"]
        or run.get("status") != "completed"
        or run.get("conclusion") != "success"
        or run.get("repository", {}).get("full_name") != REPO
    ):
        raise ReceiptError(f"run {run_id}: wrong repository/head/workflow or not successful")
    # The workflow run SHA alone does not establish that the claimed files
    # were present at that revision. Check GitHub's original Git tree too.
    historical_tree = fetcher(
        f"https://api.github.com/repos/{REPO}/git/trees/{receipt['checked_head']}?recursive=1"
    )
    if (not isinstance(historical_tree, dict)
            or historical_tree.get("truncated") is not False
            or not isinstance(historical_tree.get("tree"), list)):
        raise ReceiptError(f"run {run_id}: incomplete historical source tree")
    tree_blobs = {}
    for entry in historical_tree["tree"]:
        if isinstance(entry, dict) and entry.get("type") == "blob":
            if entry.get("path") in tree_blobs:
                raise ReceiptError(f"run {run_id}: duplicate historical Git path")
            tree_blobs[entry.get("path")] = entry.get("sha")
    for file_ref in pinned_files:
        if tree_blobs.get(file_ref["path"]) != file_ref["blob_sha"]:
            raise ReceiptError(
                f"run {run_id}: claimed blob not present at checked head: {file_ref['path']}"
            )
    jobs = fetcher(base + "/jobs?per_page=100")
    if not isinstance(jobs, dict) or not isinstance(jobs.get("jobs"), list):
        raise ReceiptError(f"run {run_id}: missing job evidence")
    if jobs.get("total_count") != len(jobs["jobs"]):
        raise ReceiptError(f"run {run_id}: paginated job results are incomplete")
    matching = [
        job for job in jobs["jobs"]
        if isinstance(job, dict) and job.get("name") == receipt["job"]
        and job.get("conclusion") == "success"
    ]
    if len(matching) != 1:
        raise ReceiptError(f"run {run_id}: required job not successful exactly once")
    steps = matching[0].get("steps", [])
    matching_steps = [
        step for step in steps
        if isinstance(step, dict) and step.get("name") == receipt["step"]
        and step.get("conclusion") == "success"
    ]
    if len(matching_steps) != 1:
        raise ReceiptError(f"run {run_id}: required proof/test step not successful")


def audit(payload: object, root: Path, fetcher=None) -> list[dict]:
    ledger = fields(payload, {"schema", "claims"}, "ledger")
    if ledger["schema"] != "eth-scoped-receipts/v1" or not isinstance(ledger["claims"], list):
        raise ReceiptError("unrecognized receipt schema or claims list")
    # No claim is a safe state. Never force a replacement receipt before its
    # new exact-head workflow run exists; removing stale claims must work.
    seen_ids: set[str] = set()
    observations: list[dict] = []
    for entry in ledger["claims"]:
        claim = fields(entry, {"id", "statement", "kind", "quantifier", "domain",
                               "observation", "excluded", "theorem", "receipt", "files"}, "claim")
        name = text_value(claim["id"], "claim id")
        if not IDENTITY.fullmatch(name) or name in seen_ids:
            raise ReceiptError(f"invalid or repeated claim ID {name}")
        seen_ids.add(name)
        for key in ("statement", "domain", "observation"):
            text_value(claim[key], f"{name}.{key}")
        kind = claim["kind"]
        if kind not in CLAIM_KINDS or claim["quantifier"] != CLAIM_KINDS[kind]:
            raise ReceiptError(f"{name}: unsupported proof tier/quantifier; no implicit promotion")
        if kind == "abstract_lean_model":
            theorem_name = text_value(claim["theorem"], f"{name}.theorem")
            if "." not in theorem_name or not all(
                part.isidentifier() for part in theorem_name.split(".")
            ):
                raise ReceiptError(f"{name}: expected fully qualified Lean theorem")
        elif claim["theorem"] is not None:
            raise ReceiptError(f"{name}: finite guard must not claim a Lean theorem")
        if not isinstance(claim["excluded"], list) or not claim["excluded"]:
            raise ReceiptError(f"{name}: excluded interpretations required")
        for exclusion in claim["excluded"]:
            text_value(exclusion, f"{name}.excluded")

        receipt = fields(claim["receipt"],
                         {"repository", "checked_head", "workflow", "run_id", "job", "step"},
                         f"{name}.receipt")
        if receipt["repository"] != REPO:
            raise ReceiptError(f"{name}: receipt from an unexpected repository")
        sha_value(receipt["checked_head"], f"{name}.checked_head")
        for key in ("workflow", "job", "step"):
            text_value(receipt[key], f"{name}.{key}")
        if not receipt["workflow"].startswith(".github/workflows/") or not receipt["workflow"].endswith(".yml"):
            raise ReceiptError(f"{name}: invalid workflow path")
        if type(receipt["run_id"]) is not int or receipt["run_id"] <= 0:
            raise ReceiptError(f"{name}: invalid workflow run ID")

        if not isinstance(claim["files"], list) or not claim["files"]:
            raise ReceiptError(f"{name}: at least one content-pinned source file required")
        seen_paths: set[str] = set()
        for file_entry in claim["files"]:
            file_ref = fields(file_entry, {"path", "blob_sha"}, f"{name}.file")
            path = text_value(file_ref["path"], f"{name}.file.path")
            sha_value(file_ref["blob_sha"], f"{name}.file.blob_sha")
            if path in seen_paths:
                raise ReceiptError(f"{name}: duplicate file pin {path}")
            seen_paths.add(path)
            observed = git_blob_sha(checked_path(root, path).read_bytes())
            if observed != file_ref["blob_sha"]:
                raise ReceiptError(f"{name}: stale source blob {path}; expected {file_ref['blob_sha']}, found {observed}")
        if kind == "abstract_lean_model":
            # The exact checked source bytes must at least contain the claimed
            # declaration and an axiom audit. This does NOT inspect the proof.
            local_name = theorem_name.rsplit(".", 1)[1]
            lean_sources = [
                checked_path(root, file_ref["path"]).read_text()
                for file_ref in claim["files"]
                if file_ref["path"].endswith(".lean")
            ]
            if not any(
                re.search(r"\btheorem\s+" + re.escape(local_name) + r"\b", source)
                and f"#print axioms {theorem_name}" in source
                for source in lean_sources
            ):
                raise ReceiptError(f"{name}: pinned Lean theorem/axiom audit not present")
        if fetcher is not None:
            verify_remote(receipt, claim["files"], fetcher)
        observations.append({
            "id": name,
            "kind": kind,
            "domain": claim["domain"],
            "quantifier": claim["quantifier"],
            "checked_head": receipt["checked_head"],
            "run_id": receipt["run_id"],
            "source_pins": "match_current_bytes",
            "remote_receipt": "workflow_job_step_passed" if fetcher else "not_checked",
            "semantic_promotion": "none",
        })
    return observations


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-remote", action="store_true",
                        help="verify workflow run, exact head, job and step against GitHub")
    parser.add_argument("--json", action="store_true", help="emit the scoped evidence inventory")
    args = parser.parse_args()
    try:
        entries = audit(json.loads(LEDGER.read_text()), ROOT,
                        fetcher=fetch_github if args.verify_remote else None)
    except (ReceiptError, OSError, ValueError) as error:
        print(f"evidence receipt refusal: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps({"schema": "eth-receipt-audit/v1", "claims": entries},
                         indent=2, sort_keys=True))
    else:
        print(f"{len(entries)} source-pinned scoped receipts checked; "
              + ("remote workflow steps verified" if args.verify_remote
                 else "remote verification not requested"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
