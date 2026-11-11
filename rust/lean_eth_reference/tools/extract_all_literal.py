#!/usr/bin/env python3
"""Strict source scanner for every fixed literal BitProgram in original OpenAI Lean.

Only concrete finite vector/match code, numeric machine dimensions and the
12 original opcodes are accepted. Does not interpret Lean expressions.
"""
from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
BASE = Path("lean/OAI/Algorithms/SubexponentialSAT")
DEFINITION = re.compile(
    r"(?m)^(?:def|abbrev)\s+(\w+)\s*:\s*(?:[\w.]+\.)?Program\s+"
    r"(\d+)\s+(\d+)\s+(\d+)\s+where\s*\n"
    r"\s+inputStack\s*:=\s*(\d+)\s*\n"
    r"\s+outputStack\s*:=\s*(\d+)\s*\n"
    r"\s+entry\s*:=\s*(\d+)\s*\n"
    r"\s+code\s*(?:q\s*:=\s*match\s*q.val\s*with|:=\s*!\[)"
)
ARITIES = {
    "halt": 0, "goto": 1, "set": 3, "copy": 3, "bnot": 3,
    "band": 4, "bor": 4, "bxor": 4, "branch": 3,
    "push": 3, "peek": 4, "pop": 4,
}
RENAMES = {"bnot": "not", "band": "and", "bor": "or", "bxor": "xor"}


def source_blob(content: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()


def parse_instr(raw: str) -> str:
    m = re.fullmatch(r"\s*\.(\w+)(?:\s+([\w\d\s]+))?\s*", raw)
    if not m or m[1] not in ARITIES:
        raise ValueError(f"unsupported source instruction: {raw!r}")
    args = (m[2] or "").split()
    if len(args) != ARITIES[m[1]]:
        raise ValueError(f"wrong instruction arity: {raw!r}")
    for j, a in enumerate(args):
        if m[1] == "set" and j == 1 and a in ("true", "false"):
            args[j] = "1" if a == "true" else "0"
        elif not a.isdecimal() or (len(a) > 1 and a[0] == "0"):
            raise ValueError(f"nonliteral instruction operand: {raw!r}")
    return ":".join([RENAMES.get(m[1], m[1]), *args])


def parse_body(s: str, position: int, label_count: int) -> list[str]:
    tail = s[position:]
    if ":= ![" in tail[:160]:
        m = re.search(r"\n\s*code := !\[(.*?)\]", tail, re.S)
        if not m:
            raise ValueError("missing fixed vector code")
        words = m[1].split(",")
    else:
        m = re.search(r"\n\s*code q := match q\.val with\n((?:\s*\|[^\n]+(?:\n|$))+)", tail)
        if not m:
            raise ValueError("missing fixed label-match code")
        words = []
        for arm in m[1].splitlines():
            v = re.fullmatch(r"\s*\|\s*(\d+|_)\s*=>\s*(\.[\w\d\s]+)", arm)
            if not v:
                raise ValueError("unsupported label-match arm")
            if v[1] != "_" and int(v[1]) != len(words):
                raise ValueError("nonsequential original label")
            if v[1] == "_" and len(words) != label_count - 1:
                raise ValueError("unsupported nonfinal fallback")
            words.append(v[2])
    if len(words) != label_count:
        raise ValueError(f"literal label count mismatch ({len(words)} != {label_count})")
    return [parse_instr(word) for word in words]


def produce(upstream: Path) -> tuple[str, str, list[str]]:
    entries = []
    failures = []
    for source in sorted((upstream / BASE).rglob("*.lean")):
        raw = source.read_bytes()
        data = raw.decode("utf-8")
        matches = list(DEFINITION.finditer(data))
        for occurrence, m in enumerate(matches):
            name, r, s, labels, inp, out, entry = m.groups()
            r, s, labels, inp, out, entry = map(int, (r, s, labels, inp, out, entry))
            relative = source.relative_to(upstream).as_posix()
            identifier = source.relative_to(upstream / BASE).with_suffix("").as_posix().replace("/", "_").replace(".", "_").lower()
            identifier = f"{identifier}_{name.lower()}_{occurrence}"
            try:
                if not (r and s and labels and r <= 256 and s <= 4096 and labels <= 8192):
                    raise ValueError("unsupported dimensions")
                if not (inp < s and out < s and entry < labels):
                    raise ValueError("invalid source ports or entry")
                instructions = parse_body(data, m.start(), labels)
            except ValueError as exc:
                failures.append(f"{relative}:{name}:{occurrence}\t{exc}")
                continue
            blob = source_blob(raw)
            table = "\n".join([
                f"PIN|{identifier}|{COMMIT}|{blob}",
                f"PROGRAM|{identifier}|{r}|{s}|{labels}|{entry}|{inp}|{out}",
                *(f"CODE|{identifier}|{i}|{item}" for i, item in enumerate(instructions)),
                f"END|{identifier}|{labels}",
            ]) + "\n"
            entries.append((identifier, relative, blob, r, s, labels, entry, inp, out, table))
    manifest = "\n".join([
        "id\tfile\tgit_blob\tr\ts\tlabels\tentry\tinput\toutput\ttable_sha256",
        *("\t".join(map(str, e[:-1])) + "\t" + hashlib.sha256(e[-1].encode()).hexdigest()
          for e in entries),
    ]) + "\n"
    # Explicit length and record delimiters. No implicit table source trust.
    bundle = f"ORIGINAL_LEAN_LITERAL_BUNDLE|1|{COMMIT}|{len(entries)}\n" + "\n".join(e[-1] for e in entries) + f"END_ORIGINAL_LEAN_LITERAL_BUNDLE|{len(entries)}\n"
    return manifest, bundle, failures


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--upstream", type=Path, required=True)
    ap.add_argument("--output-dir", type=Path, required=True)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    manifest, bundle, failures = produce(args.upstream)
    if not manifest.splitlines()[1:]:
        raise SystemExit("no literal source tables found")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, content in [("all-literal.tsv", manifest), ("all-literal.bundle", bundle)]:
        path = args.output_dir / name
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f"catalog differs from original source: {name}")
        else:
            path.write_text(content, encoding="ascii", newline="\n")
    print(f"compiled={len(manifest.splitlines())-1} unsupported={len(failures)}")
    for failure in failures:
        print(f"UNSUPPORTED\t{failure}")


if __name__ == "__main__":
    main()
