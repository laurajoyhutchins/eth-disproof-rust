#!/usr/bin/env python3
"""Create a kernel-checkable Lean witness for a serialized, source-pinned graph.

The witness reifies *only the parsed graph*, never the original physical table.
Lean then proves finite program/port/code equality against the independently
imported original program. No generated result is called certified unless
Lean actually checks this theorem. This is a bounded artifact certificate,
not a universal proof of the Python translator or of native Rust execution.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from typing import Any

from verify_source_graph import (SOURCE_SHA, MAX_INPUT_BYTES, MAX_NODES,
                                 MAX_SOURCE_LABELS, closed_keys, insist,
                                 number, parse_node)

SOURCE_NAME = re.compile(r'OAI\.Algorithms\.SubexponentialSAT(?:\.[A-Za-z_]\w*)+')
HEX40 = re.compile(r'[0-9a-f]{40}')
ID = re.compile(r'[a-z0-9_-]{1,255}')


def instruction_lean(op: tuple[str, tuple[int, ...]], r: int, s: int, labels: int) -> str:
    """Lossless Lean constructor. All numeric operands are already range-checked."""
    name, operands = op
    specs = {
        'halt': '', 'goto': 'l', 'set': 'rbl', 'copy': 'rrl',
        'not': 'rrl', 'and': 'rrrl', 'or': 'rrrl', 'xor': 'rrrl',
        'branch': 'rll', 'push': 'srl', 'peek': 'srrl', 'pop': 'srrl',
    }
    insist(name in specs and len(specs[name]) == len(operands), 'invalid instruction for certificate')
    vals = []
    for val, kind in zip(operands, specs[name]):
        bound = {'r': r, 's': s, 'l': labels, 'b': 2}[kind]
        insist(type(val) is int and 0 <= val < bound, 'out of range certificate operand')
        vals.append(('true' if val else 'false') if kind == 'b' else f'({val} : Fin {bound})')
    name = {'not': 'bnot', 'and': 'band', 'or': 'bor', 'xor': 'bxor'}.get(name, name)
    return 'Instr.' + name + ((' ' + ' '.join(vals)) if vals else '')


def read_source_graph(path: Path, record: dict[str, str]):
    for key in ('id', 'fqn', 'module', 'git_blob'):
        insist(isinstance(record.get(key), str), f'missing pinned declaration field {key}')
    insist(bool(ID.fullmatch(record['id'])) and bool(HEX40.fullmatch(record['git_blob'])),
           'invalid pinned source record')
    insist(bool(SOURCE_NAME.fullmatch(record['module'])) and
           bool(SOURCE_NAME.fullmatch(record['fqn'])), 'invalid pinned Lean name')
    raw = path.read_bytes()
    insist(0 < len(raw) <= MAX_INPUT_BYTES and raw.endswith(b'\n') and
           raw.count(b'\n') == 1 and raw.isascii(), 'noncanonical Lean source graph line')
    def strict_object(pairs):
        result: dict[str, Any] = {}
        for key, value in pairs:
            insist(key not in result, 'duplicate JSON object field')
            result[key] = value
        return result
    parsed = json.loads(raw, object_pairs_hook=strict_object)
    closed_keys(parsed, {'kind', 'source_commit', 'source_blob', 'declaration', 'id', 'abi', 'command'})
    insist(parsed['kind'] == 'original-structured-source-v1' and
           parsed['source_commit'] == SOURCE_SHA and
           parsed['source_blob'] == record['git_blob'] and
           parsed['declaration'] == record['fqn'] and
           parsed['id'] == record['id'], 'source identity differs from pinned declaration')
    abi = parsed['abi']
    closed_keys(abi, {'r', 's', 'labels', 'input', 'output'})
    r = number(abi['r'], 256, 'r')
    s = number(abi['s'], 4096, 's')
    l = number(abi['labels'], MAX_SOURCE_LABELS, 'labels')
    inp = number(abi['input'], s, 'input')
    out = number(abi['output'], s, 'output')
    insist(r > 0 and s > 0 and l > 0 and inp < s and out < s, 'invalid source graph ABI')
    root = parse_node(parsed['command'], r, s, [MAX_NODES])
    entry = root.entry(1, 0)
    insist(root.size + 1 == l and 0 <= entry < l, 'graph dimensions/entry inconsistent')
    return raw, parsed, root, (r, s, l, entry, inp, out)


def certificate_source(path: Path, record: dict[str, str]) -> tuple[str, dict[str, Any]]:
    raw, _graph, root, (r, s, l, entry, inp, out) = read_source_graph(path, record)
    # Exactly these rows, and no independent golden table, are used to build
    # the candidate that Lean must compare with its own original definition.
    rows = [('halt', ())] + [root.instr(1, 0, pc) for pc in range(1, l)]
    content = '\n'.join([
        f'import {record["module"]}',
        '',
        '-- Certificate is bound by SHA-256 in the receipt to the source JSON bytes.',
        f'-- source-graph-sha256: {hashlib.sha256(raw).hexdigest()}',
        'set_option maxHeartbeats 4000000',
        'set_option maxRecDepth 4096',
        'set_option linter.unnecessarySimpa false',
        'namespace OriginalSourceGraphKernelCertificate',
        'open OAI.Algorithms.SubexponentialSAT.BitProgram',
        f'private def candidate : Program {r} {s} {l} where',
        f'  inputStack := ({inp} : Fin {s})',
        f'  outputStack := ({out} : Fin {s})',
        f'  entry := ({entry} : Fin {l})',
        f'  code := fun pc => (#[',
        *(f'    {instruction_lean(row, r, s, l)},' for row in rows),
        f'  ] : Array (Instr {r} {s} {l}))[pc.val]\' (by simpa using pc.isLt)',
        f'private theorem input_eq : candidate.inputStack = {record["fqn"]}.inputStack := by decide',
        f'private theorem output_eq : candidate.outputStack = {record["fqn"]}.outputStack := by decide',
        f'private theorem entry_eq : candidate.entry = {record["fqn"]}.entry := by decide',
        f'private theorem all_code_eq (pc : Fin {l}) :',
        f'    candidate.code pc = {record["fqn"]}.code pc := by',
        '  fin_cases pc <;> rfl',
        f'private theorem all_steps_eq (cfg : Cfg {r} {s} {l}) :',
        f'    step candidate cfg = step {record["fqn"]} cfg := by',
        '  change cfg.pc.map (fun pc => execInstr (candidate.code pc) cfg) =',
        f'    cfg.pc.map (fun pc => execInstr ({record["fqn"]}.code pc) cfg)',
        '  have hfun :',
        f'      (fun pc : Fin {l} => execInstr (candidate.code pc) cfg) =',
        f'      (fun pc : Fin {l} => execInstr ({record["fqn"]}.code pc) cfg) := by',
        '    funext pc',
        '    exact congrArg (fun instr => execInstr instr cfg) (all_code_eq pc)',
        '  exact congrArg (fun f => cfg.pc.map f) hfun',
        'end OriginalSourceGraphKernelCertificate',
        '',
    ])
    return content, {
        'id': record['id'], 'declaration': record['fqn'],
        'source_blob': record['git_blob'], 'source_commit': SOURCE_SHA,
        'source_graph_sha256': hashlib.sha256(raw).hexdigest(),
        'certificate_sha256': hashlib.sha256(content.encode()).hexdigest(),
        'physical_labels': l,
        'coverage': 'all labels and arbitrary one-step physical states',
        'status': 'UNVERIFIED_LEAN_CERTIFICATE_SOURCE',
    }
