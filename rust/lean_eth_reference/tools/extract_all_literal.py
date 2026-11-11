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
    r"\s+code\s*(?:(\w+)\s*:=\s*match\s+(\w+)\.val\s*with|:=\s*!\[|:=\s*fun\s+(\w+)\s*=>)"
)
# Preserve the original 61-table identifiers as the extractor learns new
# finite syntax. Existing catalog IDs are stable cross-version references.
LEGACY_DEFINITION = re.compile(
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


def parse_instr(raw: str, symbols: dict[str, int]) -> str:
    m = re.fullmatch(r"\s*\.(\w+)(?:\s+([\w\d\s]+))?\s*", raw)
    if not m or m[1] not in ARITIES:
        raise ValueError(f"unsupported source instruction: {raw!r}")
    args = (m[2] or "").split()
    if len(args) != ARITIES[m[1]]:
        raise ValueError(f"wrong instruction arity: {raw!r}")
    for j, a in enumerate(args):
        if m[1] == "set" and j == 1 and a in ("true", "false"):
            args[j] = "1" if a == "true" else "0"
        elif a in symbols:
            args[j] = str(symbols[a])
        elif not a.isdecimal() or (len(a) > 1 and a[0] == "0"):
            raise ValueError(f"nonliteral instruction operand: {raw!r}")
    return ":".join([RENAMES.get(m[1], m[1]), *args])


def parse_body(s: str, position: int, label_count: int) -> list[str]:
    # Only *closed numeric Fin constants* are substituted. They are source
    # declarations, not an evaluator for arbitrary Lean expressions.
    symbols = {}
    for m in re.finditer(r"(?m)^def\s+(\w+)\s*:\s*Fin\s+(\d+)\s*:=\s*(\d+)\s*$", s[:position]):
        name, domain, value = m.groups()
        if int(domain) == label_count and int(value) < label_count:
            symbols[name] = int(value)
    tail = s[position:]
    if ":= ![" in tail[:160]:
        m = re.search(r"\n\s*code := !\[(.*?)\]", tail, re.S)
        if not m:
            raise ValueError("missing fixed vector code")
        words = m[1].split(",")
    elif re.search(r"\n\s*code\s+\w+\s*:=\s*match", tail[:180]):
        m = re.search(r"\n\s*code\s+(\w+)\s*:=\s*match\s+(\w+)\.val\s+with\n((?:[ \t]*\|[^\n]+(?:\n|$))+)", tail)
        if m and m[1] != m[2]:
            raise ValueError("match variable mismatch")
        if not m:
            raise ValueError("missing fixed label-match code")
        cases = {}
        fallback = None
        arms = m[3].splitlines()
        for pos, arm in enumerate(arms):
            v = re.fullmatch(r"\s*\|\s*(\d+|_)\s*=>\s*(\.[\w\d\s]+)", arm)
            if not v:
                raise ValueError("unsupported label-match arm")
            key, expression = v.groups()
            if key == "_":
                if pos != len(arms) - 1 or fallback is not None:
                    raise ValueError("nonfinal or repeated fallback")
                fallback = expression
            else:
                label = int(key)
                if label >= label_count or label in cases:
                    raise ValueError("duplicate or out-of-range original label")
                cases[label] = expression
        if fallback is None and len(cases) != label_count:
            raise ValueError("incomplete labels without fallback")
        words = [cases.get(i, fallback) for i in range(label_count)]
        if any(w is None for w in words):
            raise ValueError("missing original label")
    elif re.search(r"\n\s*code\s*:=\s*fun\s+\w+\s*=>", tail[:180]):
        m = re.search(r"\n\s*code\s*:=\s*fun\s+(\w+)\s*=>\s*(.*?)(?=\n\n(?:theorem|lemma|def|abbrev|end|namespace|/-|@\[)|\Z)", tail, re.S)
        if not m:
            raise ValueError("nonliteral function code")
        var, expr = m.groups()
        expr = re.sub(r"\s+", " ", expr).strip()
        words = []
        while True:
            case = re.match(r"if\s+" + re.escape(var) + r"\s*=\s*(\d+)\s+then\s+(\.\w+(?:\s+[\w]+)*)\s+else\s+", expr)
            if case is None:
                break
            if int(case[1]) != len(words):
                raise ValueError("nonconsecutive finite function case")
            words.append(case[2])
            expr = expr[case.end():]
        if not re.fullmatch(r"\.\w+(?:\s+[\w]+)*", expr):
            raise ValueError("unsupported finite function fallback")
        words.extend([expr] * (label_count - len(words)))
        if len(words) != label_count:
            raise ValueError("function emits too many finite labels")
    else:
        raise ValueError("unsupported original code constructor")
    if len(words) != label_count:
        raise ValueError(f"literal label count mismatch ({len(words)} != {label_count})")
    return [parse_instr(word, symbols) for word in words]


def produce(upstream: Path) -> tuple[str, str, list[str]]:
    entries = []
    failures = []
    for source in sorted((upstream / BASE).rglob("*.lean")):
        raw = source.read_bytes()
        data = raw.decode("utf-8")
        matches = list(DEFINITION.finditer(data))
        legacy = {m.start(): i for i, m in enumerate(LEGACY_DEFINITION.finditer(data))}
        new_ordinal = len(legacy)
        for m in matches:
            occurrence = legacy.get(m.start())
            if occurrence is None:
                occurrence = new_ordinal
                new_ordinal += 1
            name, r, s, labels, inp, out, entry = m.groups()[:7]
            r, s, labels, inp, out, entry = map(int, (r, s, labels, inp, out, entry))
            if m.group(8) != m.group(9):
                failures.append(f"{source}: match variable mismatch")
                continue
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
