#!/usr/bin/env python3
"""Pack, check, or restore portable Lean captures without invoking Lean.

Archives contain only successfully completed local captures. No backend, account,
remote service, or machine-specific storage path is part of the protocol.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import tempfile
import zipfile

from capture import SCHEMA, STAGES, canonical, digest, machine_metrics, stage_paths, validate

FORMAT = "lean-bitprogram-capture-bundle/v1"
EPOCH = (1980, 1, 1, 0, 0, 0)


def _check_stage(name: str, files: dict[str, bytes]) -> dict:
    """Verify recorded trace completeness and checksums without a Lean runtime."""
    prefix = f"runs/{name}"
    metadata = json.loads(files[prefix + ".json"])
    if metadata.get("schema") != SCHEMA or metadata.get("name") != name:
        raise ValueError(f"{name}: incompatible metadata")
    if metadata.get("exit_code") != 0:
        raise ValueError(f"{name}: run did not complete successfully")
    compressed = files[prefix + ".stdout.gz"]
    try:
        raw = gzip.decompress(compressed)
    except (OSError, EOFError) as exc:
        raise ValueError(f"{name}: invalid compressed trace") from exc
    if digest(raw) != metadata.get("stdout_sha256") or digest(compressed) != metadata.get("stdout_gzip_sha256"):
        raise ValueError(f"{name}: trace checksum mismatch")
    if digest(files[prefix + ".stderr"]) != metadata.get("stderr_sha256"):
        raise ValueError(f"{name}: stderr checksum mismatch")
    if validate(STAGES[name], raw) != metadata.get("coverage"):
        raise ValueError(f"{name}: incomplete capture")
    expected_metrics = machine_metrics(raw) if STAGES[name].kind == "machine" else None
    if metadata.get("machine_metrics") != expected_metrics:
        raise ValueError(f"{name}: incorrect derived measurements")
    if not isinstance(metadata.get("fingerprint"), str) or len(metadata["fingerprint"]) != 64:
        raise ValueError(f"{name}: missing source/runtime fingerprint")
    return metadata


def _valid_relative(path: str) -> bool:
    p = PurePosixPath(path)
    return bool(path) and not p.is_absolute() and all(
        segment not in ("", ".", "..") for segment in path.split("/")
    ) and "\\" not in path


def _inspect_files(files: dict[str, bytes]) -> list[str]:
    if any(not _valid_relative(name) for name in files):
        raise ValueError("unsafe archive member path")
    if "index.json" not in files:
        raise ValueError("missing capture index")
    index = json.loads(files["index.json"])
    if index.get("schema") != SCHEMA or not isinstance(index.get("completed"), dict):
        raise ValueError("invalid capture index")
    names = []
    for name in STAGES:
        paths = [f"runs/{name}.json", f"runs/{name}.stdout.gz", f"runs/{name}.stderr"]
        present = [p in files for p in paths]
        if any(present) and not all(present):
            raise ValueError(f"{name}: incomplete stage files")
        if all(present):
            record = _check_stage(name, files)
            if index["completed"].get(name) != record:
                raise ValueError(f"{name}: index disagrees with recorded metadata")
            names.append(name)
    if not names:
        raise ValueError("no successfully completed Lean stages to archive")
    if set(index["completed"]) != set(names):
        raise ValueError("capture index contains stale or missing stage records")
    extras = set(files) - {"index.json", "source-inventory.json"} - {
        f"runs/{name}{suffix}" for name in names
        for suffix in (".json", ".stdout.gz", ".stderr")
    }
    if extras:
        raise ValueError(f"unrecognized files in capture bundle: {sorted(extras)}")
    return names


def _zip_entry(name: str, payload: bytes) -> tuple[zipfile.ZipInfo, bytes]:
    info = zipfile.ZipInfo(name, date_time=EPOCH)
    info.compress_type = zipfile.ZIP_STORED  # stdout is already gzipped
    info.external_attr = 0o100644 << 16
    info.create_system = 3
    return info, payload


def pack(directory: Path, archive: Path) -> list[str]:
    files: dict[str, bytes] = {}
    for path in directory.rglob("*"):
        if not path.is_file() or path.is_symlink():
            continue
        rel = path.relative_to(directory).as_posix()
        if rel == "index.json" or rel == "source-inventory.json" or (
            rel.startswith("runs/") and rel.endswith((".json", ".stdout.gz", ".stderr"))
            and not ".failed." in rel
        ):
            files[rel] = path.read_bytes()
    stages = _inspect_files(files)
    descriptor = {"format": FORMAT, "schema": SCHEMA, "stages": stages,
                  "files": {name: {"sha256": digest(data), "size": len(data)}
                            for name, data in sorted(files.items())}}
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.resolve().is_relative_to(directory.resolve()):
        raise ValueError("archive must be stored outside the capture directory")
    with tempfile.NamedTemporaryFile(dir=archive.parent, prefix=".capture-bundle-", delete=False) as tmp:
        staging = Path(tmp.name)
    try:
        with zipfile.ZipFile(staging, mode="w", allowZip64=True) as z:
            for name, payload in sorted(files.items()):
                info, data = _zip_entry(name, payload)
                z.writestr(info, data)
            info, data = _zip_entry("bundle-manifest.json", canonical(descriptor))
            z.writestr(info, data)
        os.replace(staging, archive)
    finally:
        staging.unlink(missing_ok=True)
    return stages


def read_bundle(archive: Path) -> tuple[dict[str, bytes], list[str]]:
    with zipfile.ZipFile(archive, mode="r") as z:
        entries = z.infolist()
        names = [x.filename for x in entries]
        if len(names) != len(set(names)) or any(not _valid_relative(name) for name in names):
            raise ValueError("archive contains duplicated or unsafe paths")
        if "bundle-manifest.json" not in names:
            raise ValueError("missing archive manifest")
        for item in entries:
            if item.is_dir() or ((item.external_attr >> 16) & 0o170000) not in (0, 0o100000):
                raise ValueError("archive contains non-regular members")
        desc = json.loads(z.read("bundle-manifest.json"))
        if desc.get("format") != FORMAT or desc.get("schema") != SCHEMA:
            raise ValueError("unsupported archive format")
        spec = desc.get("files")
        if not isinstance(spec, dict) or set(spec) != set(names) - {"bundle-manifest.json"}:
            raise ValueError("archive contents differ from manifest")
        files: dict[str, bytes] = {}
        for item in entries:
            name = item.filename
            if name == "bundle-manifest.json":
                continue
            if not isinstance(spec[name], dict) or item.file_size != spec[name].get("size"):
                raise ValueError(f"{name}: incorrect expected size")
            data = z.read(item)
            if digest(data) != spec[name].get("sha256"):
                raise ValueError(f"{name}: file checksum mismatch")
            files[name] = data
    stages = _inspect_files(files)
    if desc.get("stages") != stages:
        raise ValueError("stage manifest differs from captured stages")
    return files, stages


def unpack(archive: Path, directory: Path) -> list[str]:
    files, stages = read_bundle(archive)  # fail closed before writing anything
    if directory.exists() and any(directory.iterdir()):
        raise ValueError("destination is not empty; refusing to overwrite captures")
    directory.mkdir(parents=True, exist_ok=True)
    for name, payload in sorted(files.items()):
        path = directory / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
    return stages


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("pack")
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "lean-captures")
    p.add_argument("--archive", type=Path, required=True)
    p = sub.add_parser("verify")
    p.add_argument("--archive", type=Path, required=True)
    p = sub.add_parser("unpack")
    p.add_argument("--archive", type=Path, required=True)
    p.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "lean-captures")
    args = parser.parse_args()
    try:
        if args.action == "pack":
            stages = pack(args.out, args.archive)
        elif args.action == "verify":
            _, stages = read_bundle(args.archive)
        else:
            stages = unpack(args.archive, args.out)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile, json.JSONDecodeError) as exc:
        parser.exit(1, f"ERROR: {exc}\n")
    print(f"{args.action.upper()}: {len(stages)} verified stages: {', '.join(stages)}")


if __name__ == "__main__":
    main()
