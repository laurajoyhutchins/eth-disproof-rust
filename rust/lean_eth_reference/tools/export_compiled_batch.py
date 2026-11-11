#!/usr/bin/env python3
"""Export closed original Lean compiled programs and generate provenance-bound tables.

Requires the pinned original git checkout, a working Lean 4.34.1/Mathlib Lake
project, and an original-source OAI symlink. Each candidate is independently
elaborated and either produces a fully checked finite table or a typed refusal.
A matched PIN line alone is not a certificate of provenance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any

from extract_compiled_catalog import SOURCE_SHA, discover, blob_hash

MATHLIB_SHA = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
OPCODES = {
    'halt': '', 'goto': 'l', 'set': 'rbl',
    'copy': 'rrl', 'not': 'rrl', 'and': 'rrrl',
    'or': 'rrrl', 'xor': 'rrrl', 'branch': 'rll',
    'push': 'srl', 'peek': 'srrl', 'pop': 'srrl',
}
BASE = Path(__file__).resolve().parent
LEAN_EXPORTER = BASE / 'export_source_program.lean'
MAX_PROGRAM_BYTES = 32_000_000


def run(*argv: str, cwd: Path, timeout: int = 30) -> str:
    result = subprocess.run(argv, cwd=cwd, text=True, capture_output=True,
                            timeout=timeout)
    if result.returncode:
        raise ValueError(
            f"command {argv!r} exited {result.returncode}; "
            f"stdout={result.stdout[-1200:]!r}; stderr={result.stderr[-1200:]!r}"
        )
    return result.stdout.strip()


def ensure_pinned(upstream: Path, lake: Path) -> dict[str, str]:
    upstream = upstream.resolve()
    lake = lake.resolve()
    if not (lake / 'OAI').is_symlink():
        raise ValueError('pinned Lake project must symlink original OAI sources')
    if (lake / 'OAI').resolve() != (upstream / 'lean/OAI').resolve():
        raise ValueError('Lake source module mapping differs from pinned OAI checkout')
    if run('git', 'rev-parse', 'HEAD', cwd=upstream) != SOURCE_SHA:
        raise ValueError('wrong original OpenAI source commit')
    if run('git','status','--porcelain','--untracked-files=no',cwd=upstream):
        raise ValueError('original OpenAI tracked sources have modifications')
    mathlib=lake/'.lake/packages/mathlib'
    if not mathlib.is_dir() or run('git','rev-parse','HEAD',cwd=mathlib) != MATHLIB_SHA:
        raise ValueError('wrong or absent pinned Mathlib checkout')
    if run('git','status','--porcelain','--untracked-files=no',cwd=mathlib):
        raise ValueError('pinned Mathlib has tracked modifications')
    version=run('lake','env','lean','--version',cwd=lake)
    if not version.startswith('Lean (version 4.34.1,'):
        raise ValueError(f'incorrect Lean toolchain {version}')
    return {'source_commit':SOURCE_SHA,'mathlib_commit':MATHLIB_SHA,'lean':version}


def probe_source(record: dict[str,str]) -> str:
    for field in ('module','fqn','id','git_blob'):
        if field not in record:raise ValueError(f'missing source field {field}')
    if not re.fullmatch(r'OAI\.Algorithms\.SubexponentialSAT(?:\.[A-Za-z_]\w*)+',record['module']):
        raise ValueError('invalid original source module')
    if not re.fullmatch(r'OAI\.Algorithms\.SubexponentialSAT(?:\.[A-Za-z_]\w*)+',record['fqn']):
        raise ValueError('invalid original source declaration')
    if not re.fullmatch(r'[a-z0-9_-]+',record['id']):
        raise ValueError('invalid source id')
    if not re.fullmatch(r'[0-9a-f]{40}',record['git_blob']):
        raise ValueError('invalid Git source blob')
    source = LEAN_EXPORTER.read_text(encoding='utf8')
    # Only exact compiler input source is interpolated, not arbitrary executable
    # Lean code or host-provided callback expressions.
    return (f"import {record['module']}\n" + source + '\n'
            # Retain Lean's deterministic heartbeat accounting, but give
            # compiled source programs more than the interactive default.
            # The subprocess wall-clock limit remains authoritative.
            "set_option maxHeartbeats 2000000\n"
            f"#export_original_program {record['fqn']} \"{record['id']}\" \"{record['git_blob']}\"\n")


def validate_table(raw: str, record: dict[str, str], max_labels: int) -> tuple[int,...]:
    if len(raw.encode('utf-8')) > MAX_PROGRAM_BYTES or not raw.isascii() or '\r' in raw:
        raise ValueError('noncanonical or over-budget source table')
    if not raw.endswith('\n'):
        raise ValueError('source table does not end in newline')
    lines=raw[:-1].split('\n')
    label=record['id']
    expected=f"PIN|{label}|{SOURCE_SHA}|{record['git_blob']}"
    if not lines or lines[0]!=expected:
        raise ValueError('source identity or PIN mismatch')
    header=lines[1].split('|') if len(lines)>1 else []
    if len(header)!=8 or header[:2]!=['PROGRAM',label]:
        raise ValueError('invalid source machine header')
    def number(value: str) -> int:
        if not re.fullmatch(r'(?:0|[1-9][0-9]*)',value):
            raise ValueError('noncanonical source machine operand')
        return int(value)
    r,s,l,entry,inp,out=tuple(map(number,header[2:]))
    if not (0<r<=256 and 0<s<=4096 and 0<l<=max_labels and entry<l and inp<s and out<s):
        raise ValueError('source machine dimensions outside bounded ABI')
    if len(lines)!=l+3 or lines[-1]!=f'END|{label}|{l}':
        raise ValueError('missing, excess or incomplete original instruction records')
    bounds={'r':r,'s':s,'l':l,'b':2}
    for i,row in enumerate(lines[2:-1]):
        fields=row.split('|')
        if len(fields)!=4 or fields[:3]!=['CODE',label,str(i)]:
            raise ValueError(f'missing or unordered original instruction {i}')
        fields=fields[3].split(':')
        kinds=OPCODES.get(fields[0])
        if kinds is None or len(fields)!=len(kinds)+1:
            raise ValueError(f'unknown original source instruction {i}')
        for value,kind in zip(fields[1:],kinds):
            if number(value)>=bounds[kind]:
                raise ValueError(f'out-of-bounds source instruction {i}')
    return r,s,l,entry,inp,out


def atomic_write(path: Path, data: str) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w',encoding='utf-8',newline='\n',
                                     dir=path.parent,prefix='.'+path.name,
                                     delete=False) as stream:
        temporary=Path(stream.name)
        try:
            stream.write(data)
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def export_one(record: dict[str,str], lake: Path, dest: Path,
               max_labels: int, timeout: int, build: bool) -> dict[str, Any]:
    name=record['id']
    # A refusal must never leave an earlier attempt's apparent success.
    (dest / f'{name}.table').unlink(missing_ok=True)
    (dest / f'{name}.receipt.json').unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(prefix='original-lean-probe-') as scratch:
        probe=Path(scratch)/'Export.lean'
        probe.write_text(probe_source(record),encoding='utf-8')
        if build:
            run('lake','-K','maxJobs=2','build',record['module'],cwd=lake,timeout=timeout)
        result=subprocess.run(['lake','env','lean',str(probe)],cwd=lake,
                              capture_output=True,text=True,timeout=timeout,
                              env={**os.environ,'ORIGINAL_MAX_LABELS':str(max_labels)})
        if result.returncode:
            raise ValueError(
                f'Lean elaboration exited {result.returncode}; '
                f'stdout={result.stdout[-1200:]!r}; stderr={result.stderr[-1200:]!r}'
            )
        raw=result.stdout
        abi=validate_table(raw,record,max_labels)
        table_path=dest/f'{name}.table'
        atomic_write(table_path,raw)
        receipt={'id':name,'module':record['module'],'declaration':record['fqn'],
                 'source_commit':SOURCE_SHA,'source_git_blob':record['git_blob'],
                 'sha256':hashlib.sha256(raw.encode('ascii')).hexdigest(),
                 'bytes':len(raw.encode('ascii')),
                 'abi':{'registers':abi[0],'stacks':abi[1],'labels':abi[2],
                        'entry':abi[3],'input':abi[4],'output':abi[5]},
                 'status':'EXPORTED_FROM_PINNED_LEAN'}
        atomic_write(table_path.with_suffix('.receipt.json'),
                     json.dumps(receipt,indent=2,sort_keys=True)+'\n')
        return receipt


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True)
    p.add_argument('--lake-root',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--query-closure',action='store_true')
    p.add_argument('--max-labels',type=int,default=8192)
    p.add_argument('--timeout-seconds',type=int,default=120)
    p.add_argument('--limit',type=int,default=12)
    p.add_argument('--start',type=int,default=0)
    p.add_argument('--name-regex',default='')
    p.add_argument('--no-build',action='store_true')
    p.add_argument('--probe-only',action='store_true',
                   help='write probe source for review, never claim genuine export')
    args=p.parse_args()
    if not (1<=args.max_labels<=50000 and 1<=args.limit<=100 and args.timeout_seconds>=2 and args.start>=0):
        p.error('invalid bounded program budget')
    result=discover(args.upstream,args.query_closure)
    selected=result['candidates']
    if args.name_regex:
        pattern=re.compile(args.name_regex)
        selected=[x for x in selected if pattern.search(x['fqn'])]
    selected=selected[args.start:args.start+args.limit]
    if not selected:raise SystemExit('no matching closed original-source programs')
    for x in selected:
        source=args.upstream/x['file']
        if blob_hash(source.read_bytes())!=x['git_blob']:
            raise SystemExit(f'original source changed: {x["file"]}')
    args.output_dir.mkdir(parents=True,exist_ok=True)
    if args.probe_only:
        for x in selected:
            atomic_write(args.output_dir/(x['id']+'.lean'),probe_source(x))
        print(f'PROBE_ONLY count={len(selected)}; no original tables or Rust generated')
        return
    pins=ensure_pinned(args.upstream,args.lake_root)
    completed=[]; refused=[]
    for rec in selected:
        try:
            proof=export_one(rec,args.lake_root,args.output_dir,args.max_labels,
                             args.timeout_seconds,not args.no_build)
            completed.append(proof)
            print(f"EXPORTED {rec['id']} labels={proof['abi']['labels']} sha256={proof['sha256']}",flush=True)
        except (ValueError,subprocess.TimeoutExpired,subprocess.CalledProcessError,OSError) as exc:
            refused.append({'id':rec['id'],'reason':type(exc).__name__,
                            'detail':str(exc)[-1000:]})
            print(f"REFUSED {rec['id']} {type(exc).__name__}: {str(exc)[-170:]}",flush=True)
    report={'kind':'original-source-program-export','pins':pins,
            'attempted':len(selected),'exported':completed,'refused':refused}
    atomic_write(args.output_dir/'batch-report.json',json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'RESULT exported={len(completed)} refused={len(refused)} attempted={len(selected)}')
    if not completed:raise SystemExit('No verified original machine tables; refusing apparent success')

if __name__=='__main__':main()
