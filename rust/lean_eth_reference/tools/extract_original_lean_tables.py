#!/usr/bin/env python3
"""Fail-closed extraction of three literal original OpenAI Lean BitProgram tables.

Only fixed constructor tables are supported: no symbolic reduction, callbacks,
proofs, noncomputable definitions or guessed control flow.
"""
from __future__ import annotations

import argparse
import hashlib
import re
from pathlib import Path

SOURCE_COMMIT = '4eaee87548250b2682affda7d05d947c05554bae'
PROGRAMS = {
    'binary-add': ('BinaryPrograms.lean', 'ab8a858c2466aa3879087f825802aa76c7aa768f', 'def program : SubexponentialSAT.BitProgram.Program 8 3 13 where', (8,3,13,0,0,2), 'match'),
    'query-parity': ('SqrtLogSpace/QueryProgram.lean', '7a2535f7c479463a5f5ed8a30a33192aad1b063e', 'def parityProgram : Program 3 1 4 where', (3,1,4,0,0,0), 'vector'),
    'type-bit': ('Subexp/TypeBitProgram.lean', '4e020c828e458b4420179da94c3451bea653a7b9', 'abbrev program : Program 3 2 7 where', (3,2,7,0,1,1), 'vector'),
}
OPCODES = {'halt': 0, 'goto':1, 'set':3, 'copy':3, 'bnot':3, 'band':4, 'bor':4, 'bxor':4, 'branch':3, 'push':3, 'peek':4, 'pop':4}
MAP = {'bnot':'not','band':'and','bor':'or','bxor':'xor'}


def git_blob(content: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest()


def parse_instruction(t: str) -> str:
    m = re.fullmatch(r'\.([a-z]+)(?:\s+([0-9]+(?:\s+[0-9]+)*))?', t.strip())
    if not m or m[1] not in OPCODES:
        raise ValueError('unsupported literal instruction: '+repr(t))
    args = (m[2] or '').split()
    if len(args) != OPCODES[m[1]]:
        raise ValueError('wrong literal opcode arity: '+repr(t))
    return ':'.join([MAP.get(m[1],m[1]), *args])


def extract(root: Path, name: str) -> str:
    path, blob, needle, shape, style = PROGRAMS[name]
    source = (root/'lean'/'OAI'/'Algorithms'/'SubexponentialSAT'/path).read_bytes()
    if git_blob(source) != blob:
        raise ValueError(f'{name}: original pinned Lean source Git blob mismatch')
    text = source.decode('utf-8')
    if text.count(needle) != 1:
        raise ValueError(f'{name}: expected unique source declaration')
    body = text.split(needle, 1)[1].split('\n\ndef ',1)[0].split('\n\nabbrev ',1)[0]
    r, s, labels, entry, input_port, output_port = shape
    for field,value in [('inputStack',input_port),('outputStack',output_port),('entry',entry)]:
        m = re.search(r'^  '+field+r' := (\d+)\s*$', body, flags=re.M)
        if m is None or int(m[1]) != value:
            raise ValueError(f'{name}: original source ABI changed at {field}')
    if style == 'vector':
        m = re.search(r'\n  code := !\[(.*?)\]',body, flags=re.S)
        if not m: raise ValueError(f'{name}: missing literal code vector')
        instructions = [parse_instruction(x) for x in m[1].split(',')]
    else:
        m = re.search(r'\n  code q := match q\.val with\n((?:    \|[^\n]+(?:\n|$))+)',body)
        if not m: raise ValueError(f'{name}: missing literal match code')
        instructions = []
        seen=set()
        for line in m[1].splitlines():
            item=re.fullmatch(r'    \| (\d+|_) => (\.[a-z]+(?:\s+[\d ]+)?)',line)
            if not item: raise ValueError(f'{name}: unsupported match arm '+line)
            label,raw=item.groups()
            if label == '_':
                if len(instructions) != labels-1 or parse_instruction(raw)!='halt':
                    raise ValueError('nonterminal fallback not supported')
                instructions.append('halt')
            else:
                if int(label) != len(instructions) or label in seen:
                    raise ValueError('non-contiguous or duplicated match arm')
                seen.add(label)
                instructions.append(parse_instruction(raw))
    if len(instructions) != labels:
        raise ValueError(f'{name}: labels differ ({len(instructions)} != {labels})')
    return '\n'.join([
       f'PIN|{name}|{SOURCE_COMMIT}|{blob}',
       f'PROGRAM|{name}|{r}|{s}|{labels}|{entry}|{input_port}|{output_port}',
       *[f'CODE|{name}|{i}|{instr}' for i,instr in enumerate(instructions)],
       f'END|{name}|{labels}', '',
    ])


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    args=p.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name in PROGRAMS:
        data=extract(args.upstream,name)
        (args.output_dir/(name+'.table')).write_text(data,encoding='ascii',newline='\n')
        print(name, hashlib.sha256(data.encode()).hexdigest(), len(data))


if __name__=='__main__': main()
