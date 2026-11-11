#!/usr/bin/env python3
"""Lease-guarded cleanup of obsolete external CI from all Git branch histories."""
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = "laurajoyhutchins/eth-disproof-rust"
CLEAN_TREE = "63b93f13ef9a7521140fa5e19d99ede96ba33274"
ROOT = "9e45801a26944f97c48a6047e2495dae750e87e5"

FILE_INFO = r'''
name = filename.lower()
ci_word = re.compile(br'(?:cloud[ _-]*build|cloudbuild|gcloud|google[ _-]*cloud|\bgcp\b|nonexp-sudoku-(?:pr|main)-(?:rust|checkpoint))', re.I)
if (re.search(br'cloud[ _-]*build', name)
    or name == b'.github/workflows/history-rewrite-once.yml'
    or name == b'scripts/rewrite_eth_history.py'
    or (name.startswith(b'.github/workflows/') and b'gcp' in name)):
  return (None, mode, blob_id)
if name.startswith(b'.github/workflows/') or (name.startswith(b'scripts/') and name.endswith((b'.py', b'.sh'))):
  data = value.get_contents_by_identifier(blob_id)
  if ci_word.search(data):
    return (None, mode, blob_id)
if name.endswith((b'.md',b'.rst',b'.txt')):
  data = value.get_contents_by_identifier(blob_id)
  if ci_word.search(data):
    result = b''.join(line for line in data.splitlines(keepends=True) if not ci_word.search(line))
    blob_id = value.insert_file_with_contents(result)
return (filename, mode, blob_id)
'''
MESSAGE = r'''
pattern = re.compile(br'(?:cloud[ _-]*build|cloudbuild|gcloud|google[ _-]*cloud|\bgcp\b)', re.I)
lines = [line for line in message.splitlines(keepends=True) if not pattern.search(line)]
clean = b''.join(lines).strip()
if not clean:
  clean = b'ci: verification checkpoint'
return clean + b'\n'
'''
TAG_MESSAGE = r'''
pattern = re.compile(br'(?:cloud[ _-]*build|cloudbuild|gcloud|google[ _-]*cloud|\bgcp\b)', re.I)
tag.message = b''.join(line for line in tag.message.splitlines(keepends=True) if not pattern.search(line)).strip() or b'Research checkpoint'
'''

def run(*args, cwd=None, capture=False):
    result = subprocess.run(args, cwd=cwd, text=True, check=True,
                            stdout=subprocess.PIPE if capture else None)
    return result.stdout.strip() if capture else None

def main():
    mode = os.environ.get("REWRITE_MODE")
    assert mode in ("dry-run", "apply"), "Choose dry-run or apply"
    assert os.environ.get("GITHUB_REPOSITORY") == REPO, "Unexpected repository"
    assert os.environ.get("GITHUB_REF") == "refs/heads/main", "Need accepted main"
    assert os.environ.get("GITHUB_RUN_ATTEMPT") == "1", "Run attempt changed"
    expected = os.environ.get("REWRITE_EXPECTED_HEAD")
    assert bool(re.fullmatch("[0-9a-f]{40}", expected or "")), "Missing commit lease"
    run("git", "merge-base", "--is-ancestor", ROOT, expected)
    assert run("git", "rev-parse", "HEAD", capture=True) == expected, "Wrong source checkout"
    wd = Path(os.environ["RUNNER_TEMP"]) / "eth-history"
    wd.mkdir(parents=True, exist_ok=False)
    mirror = wd / "repo.git"
    run("git", "clone", "--mirror", "--quiet", f"https://github.com/{REPO}.git", str(mirror))
    original = run("git", "for-each-ref", "--format=%(refname) %(objectname)",
                   "refs/heads", "refs/tags", cwd=mirror, capture=True)
    refs = dict(line.split() for line in original.splitlines())
    assert refs.get("refs/heads/main") == expected, "Remote main advanced"
    assert len(refs) >= 20, "Unexpectedly small branch inventory"
    assert all(re.fullmatch("[0-9a-f]{40}", v) for v in refs.values())
    removed = [ref for ref in refs if "cloudbuild" in ref.lower()
               or "ops/rewrite-cloud-ci-history-" in ref.lower()]
    Path(os.environ["RUNNER_TEMP"], "eth-refs-before.txt").write_text(original + "\n")
    bundle = Path(os.environ["RUNNER_TEMP"]) / "eth-before.bundle"
    run("git", "bundle", "create", str(bundle), "--all", cwd=mirror)
    pull_refs = run("git", "for-each-ref", "--format=%(refname)", "refs/pull",
                    cwd=mirror, capture=True)
    for ref in pull_refs.splitlines():
        run("git", "update-ref", "-d", ref, cwd=mirror)
    print("Before filtering:", len(refs), "heads/tags;", len(removed), "retired refs")
    run("git", "filter-repo", "--force", "--file-info-callback", FILE_INFO,
        "--message-callback", MESSAGE, "--tag-callback", TAG_MESSAGE, cwd=mirror)
    for ref in removed:
        if subprocess.run(["git", "show-ref", "--verify", "--quiet", ref],
                          cwd=mirror).returncode == 0:
            run("git", "update-ref", "-d", ref, cwd=mirror)
    updated = run("git", "for-each-ref", "--format=%(refname) %(objectname)",
                  "refs/heads", "refs/tags", cwd=mirror, capture=True)
    newrefs = dict(line.split() for line in updated.splitlines())
    assert set(newrefs) == set(refs) - set(removed), "Ref coverage mismatch"
    tree = run("git", "rev-parse", "refs/heads/main^{tree}", cwd=mirror, capture=True)
    assert tree == CLEAN_TREE, f"Main implementation tree unexpectedly changed: {tree}"
    names = run("git", "log", "--all", "--format=", "--name-only", cwd=mirror, capture=True)
    assert not re.search(r"cloud[ _-]*build|cloudbuild|\.github/workflows/[^\n]*gcp",
                         names, re.I), "Old CI path remains reachable"
    messages = run("git", "log", "--all", "--format=%B", cwd=mirror, capture=True)
    assert not re.search(r"cloud[ _-]*build|cloudbuild|\bgcp\b|gcloud", messages, re.I), "Old CI message remains"
    print("After filtering:", len(newrefs), "refs; current tree preserved:", tree)
    for ref in sorted(removed):
        print("Retired ref:", ref)
    if mode == "dry-run":
        print("DRY RUN: remote was not modified")
        return
    run("git", "remote", "add", "origin", f"https://github.com/{REPO}.git", cwd=mirror)
    args = ["git", "push", "--porcelain", "--atomic"]
    for ref, old in sorted(refs.items()):
        args.append(f"--force-with-lease={ref}:{old}")
    args.append("origin")
    for ref in sorted(newrefs):
        args.append(f"+{ref}:{ref}")
    for ref in sorted(removed):
        args.append(f":{ref}")
    run(*args, cwd=mirror)
    print("ATOMIC_REWRITE_PUBLISHED", newrefs["refs/heads/main"])
    remote_lines = run("git", "ls-remote", "--heads", f"https://github.com/{REPO}.git",
                       cwd=mirror, capture=True)
    remote = {name: sha for sha, name in (line.split() for line in remote_lines.splitlines())}
    assert all(remote.get(ref) == sha for ref, sha in newrefs.items()
               if ref.startswith("refs/heads/")), "Remote verification mismatch"
    assert not any(ref in remote for ref in removed), "Deleted ref reappeared"
    print("REMOTE_READBACK_VERIFIED", len(remote), "branch heads")

if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.CalledProcessError, AssertionError) as exc:
        print("ABORT:", str(exc), file=sys.stderr)
        raise
