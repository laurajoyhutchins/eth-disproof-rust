#!/usr/bin/env python3
"""Kernel-checkable source comparison for Rust-emitted *physical program data*.

This adapter does not implement a second opcode decoder or a second Lean table
serializer. Both are shared with original-source-graph certificates. The Rust
producer is *not* allowed to supply Lean proof text. Original OpenAI Lean
source is the authority for every equality below.
"""
from __future__ import annotations

import sys
from pathlib import Path
from typing import Any

from source_graph_kernel_certificate import physical_program_definition
from verify_source_graph import (
    SOURCE_SHA, closed_keys, insist, number, parse_program,
    parse_source_graph_json,
)

# The physical caller ABI is independently pinned here. The callbacks remain
# source-specific; only the lifted reader and single-Call compilation are
# checked by this receipt.
CASES = {
    'dedup': (15, 16, 0, 1, 14, 13, 15, 13, 13),
    'filter': (15, 16, 0, 1, 14, 13, 15, 13, 15),
    'relation': (15, 12, 12, 13, 14, 10, 11, 10, 11),
    'tautology': (13, 11, 10, 11, 12, 0, 1, 0, 0),
    'membership': (7, 5, 5, 6, 4, 0, 1, 0, 1),
    'reversal': (3, 4, 0, 1, 2, 0, 3, 0, 2),
}
PORT_FIELDS = ('tag', 'present', 'found', 'source', 'payload', 'input', 'output')


def certificate_source(raw: bytes) -> str:
    receipt = parse_source_graph_json(raw)
    closed_keys(receipt, {'kind', 'source_commit', 'cases'})
    insist(receipt['kind'] == 'rust-physical-programs-v1',
           'unsupported Rust physical receipt format')
    insist(receipt['source_commit'] == SOURCE_SHA,
           'Rust physical receipt has wrong original source pin')
    cases = receipt['cases']
    insist(type(cases) is list and len(cases) == len(CASES),
           'Rust physical receipt is missing or duplicating a caller')
    seen: set[str] = set()
    lines = [
        'namespace OAI.Algorithms.SubexponentialSAT.LeanRustRefinement',
        'open BitProgram',
        '-- Rust-emitted physical tables checked against the pinned Lean source.',
    ]
    for case in cases:
        insist(type(case) is dict, 'Rust physical case must be an object')
        closed_keys(case, {'name', 'ports', 'lifted', 'compiled'})
        name = case['name']
        insist(type(name) is str and name in CASES and name not in seen,
               'unknown or duplicated Rust physical caller')
        seen.add(name)
        r, s, tag, present, found, source, payload, inp, out = CASES[name]
        supplied = case['ports']
        closed_keys(supplied, set(PORT_FIELDS))
        expected = (tag, present, found, source, payload, inp, out)
        observed = tuple(number(supplied[field], max(r, s), field)
                         for field in PORT_FIELDS)
        insist(observed == expected, 'Rust caller port mapping drifted')

        lifted = parse_program(case['lifted'], [1])
        compiled = parse_program(case['compiled'], [1])
        insist(lifted.kind == 'table' and compiled.kind == 'table',
               'expected physical tables, not interpreted linked program')
        insist((lifted.r, lifted.s, lifted.labels, lifted.input, lifted.output)
               == (r, s, 7, source, payload),
               'Rust lifted-reader dimensions or I/O differ')
        insist((compiled.r, compiled.s, compiled.labels, compiled.input,
                compiled.output) == (r, s, 8, inp, out),
               'Rust compiled-call dimensions or I/O differ')

        lines.extend([
            f'private def ports_{name} : RecordPrograms.Ports {r} {s} where',
            f'  tag := {tag}',
            f'  present := {present}',
            f'  found := {found}',
            f'  source := {source}',
            f'  payload := {payload}',
            '  tag_ne_present := by decide',
            '  found_ne_tag := by decide',
            '  found_ne_present := by decide',
            '  source_ne_payload := by decide',
        ])

        for prefix, program, target, rhs in (
            ('lift', lifted, 'mappedFrameProgram', f'ports_{name}'),
            ('compiled', compiled, 'mappedCompiledFrameProgram',
             f'ports_{name} {inp} {out}'),
        ):
            binding = f'rust_{prefix}_{name}'
            lines.extend(physical_program_definition(
                binding, r, s, program.labels, program.entry,
                program.input, program.output, list(program.rows)))
            lines.extend([
                f'private theorem {binding}_eq : {binding} = {target} {rhs} := by',
                '  apply program_eq_of_fields',
                '  · rfl',
                '  · rfl',
                '  · rfl',
                '  · intro pc',
                '    fin_cases pc <;> rfl',
            ])
        lines.extend([
            f'theorem rust_lift_{name}_source : rust_lift_{name} = '
            'ProgramLinking.liftProgram ParserProgram.frameProgram '
            f'(RecordPrograms.registerMap ports_{name}) '
            f'(RecordPrograms.stackMap ports_{name}) := by',
            f'  rw [rust_lift_{name}_eq, mappedFrameProgram_eq_source]',
            f'theorem rust_compiled_{name}_source : rust_compiled_{name} = '
            f'StructuredCalls.compiled (.call (mappedFrameProgram ports_{name})) '
            f'{inp} {out} := by',
            f'  rw [rust_compiled_{name}_eq, mappedCompiledFrameProgram_eq_source]',
        ])
    insist(seen == set(CASES), 'missing original physical caller')
    lines.extend([
        'end OAI.Algorithms.SubexponentialSAT.LeanRustRefinement',
        '',
    ])
    return '\n'.join(lines)


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('usage: verify_rust_physical_receipt.py RUST-PROGRAMS.json')
    # This tool verifies data only; Lean elaboration and kernel acceptance
    # happen separately and must not be inferred from this program exiting 0.
    print(certificate_source(Path(sys.argv[1]).read_bytes()), end='')


if __name__ == '__main__':
    main()
