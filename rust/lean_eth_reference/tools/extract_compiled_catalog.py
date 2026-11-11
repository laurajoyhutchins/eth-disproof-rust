#!/usr/bin/env python3
"""Discover closed source-compiled Lean BitProgram declarations in a pinned source tree.

This is a discovery index, NOT the compiled instruction stream. The latter
must come from the original Lean elaborator under the pinned Mathlib runtime.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

SOURCE_SHA = '4eaee87548250b2682affda7d05d947c05554bae'
BASE = Path('lean/OAI/Algorithms/SubexponentialSAT')
MOD_PREFIX = 'OAI.Algorithms.SubexponentialSAT'
DECL = re.compile(r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s+([A-Za-z][A-Za-z_0-9]*)\s*(?::[^=\n]+)?\s*:=\s*compiled\b')
OPEN_NS = re.compile(r'^\s*namespace\s+([A-Za-z_][\w\.]*)\s*(?:--.*)?$')
OPEN_SECTION = re.compile(r'^\s*(?:private\s+)?section(?:\s+(\w+))?\s*(?:--.*)?$')
CLOSE = re.compile(r'^\s*end(?:\s+([A-Za-z_][\w\.]*))?\s*(?:--.*)?$')
IMPORT = re.compile(r'(?m)^import\s+(OAI\.Algorithms\.SubexponentialSAT\.[\w\.]+)\s*$')


def blob_hash(raw: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()


def namespaces(src: str, decl_start: int) -> tuple[str, ...]:
    # A deliberately conservative lexical scope tracker; reject unmatched ends.
    scope: list[tuple[str, str]] = []
    for line in src[:decl_start].splitlines():
        m=OPEN_NS.fullmatch(line)
        if m:
            scope.append(('namespace', m[1]))
            continue
        m=OPEN_SECTION.fullmatch(line)
        if m:
            scope.append(('section',m[1] or ''))
            continue
        m=CLOSE.fullmatch(line)
        if not m:
            continue
        if not scope:
            raise ValueError('unmatched end before source program')
        typ, name=scope.pop()
        if m[1] and m[1]!=name and m[1]!=name.rsplit('.',1)[-1]:
            raise ValueError(f'mismatched end {m[1]} versus {name}')
    return tuple(name for typ,name in scope if typ=='namespace')


def discover(upstream: Path, query_only: bool = False) -> dict:
    files = sorted((upstream/BASE).rglob('*.lean'))
    file_map = {}
    for f in files:
        raw=f.read_bytes()
        text=raw.decode('utf-8')
        relative=f.relative_to(upstream).as_posix()
        module=MOD_PREFIX+'.'+f.relative_to(upstream/BASE).with_suffix('').as_posix().replace('/','.')
        file_map[module]={'path':relative,'blob':blob_hash(raw),'text':text,
                          'imports':IMPORT.findall(text)}
    wanted=set(file_map)
    if query_only:
        wanted=set()
        def visit(mod: str):
            if mod in wanted or mod not in file_map:return
            wanted.add(mod)
            for child in file_map[mod]['imports']:visit(child)
        visit(MOD_PREFIX+'.SqrtLogSpace.QueryStreamProgram')
    candidates=[]
    refusals=[]
    for module in sorted(wanted):
        file=file_map[module]
        text=file['text']
        for occurrence,match in enumerate(DECL.finditer(text)):
            try:
                ns=namespaces(text,match.start())
                if not ns or not ns[0].startswith('OAI'):
                    raise ValueError('missing original source namespace')
                fqn='.'.join((*ns,match[1]))
                if not re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+',fqn):
                    raise ValueError('not a qualified closed symbol')
                if any(rec['fqn']==fqn for rec in candidates):
                    raise ValueError('duplicate qualified source constant')
                id=f"{module.removeprefix(MOD_PREFIX+'.').replace('.','_').lower()}_{match[1].lower()}_{occurrence}"
                candidates.append(dict(id=id,module=module,decl=match[1],fqn=fqn,
                                       file=file['path'],git_blob=file['blob'],
                                       source_commit=SOURCE_SHA))
            except ValueError as exc:
                refusals.append(f"{file['path']}:{match[1]}:{exc}")
    return {'source_commit':SOURCE_SHA,'scope':'query-closure' if query_only else 'all',
            'files':len(wanted),'candidates':candidates,'unsupported':refusals}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--upstream',required=True,type=Path)
    p.add_argument('--query-closure',action='store_true')
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    r=discover(a.upstream,a.query_closure)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(f"source_files={r['files']} compiled_candidates={len(r['candidates'])} discovery_refusals={len(r['unsupported'])}")
    for x in r['unsupported'][:30]:print('UNSUPPORTED',x)
if __name__=='__main__':main()
