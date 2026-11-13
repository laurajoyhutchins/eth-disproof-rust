#!/usr/bin/env python3
"""Structural acceptance for original SqrtLog.Setup.computeLProgram.

The original Lean elaborator reflects composed commands without flattening the
parent physical instruction table. This gate cannot replace independent
physical-label or original-Lean state parity: the prior original table export
refused this declaration at its heartbeat budget. Unknown/malformed source
structure, wrong dimensions, and failed Rust execution are hard refusals.
"""
from __future__ import annotations
from temporary_rust_crate import isolated_cargo_manifest

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from export_compiled_batch import ensure_pinned, atomic_write
from extract_compiled_catalog import blob_hash, discover
from run_source_graph_batch import source as probe_source
from verify_source_graph import (
    SOURCE_SHA, MAX_NODES,
    closed_keys, parse_node, insist,
)

TARGET='OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.computeLProgram'
TARGET_LABELS=212


def structural_summary(raw: str, record: dict) -> tuple[dict, object]:
    insist(raw.endswith('\n') and raw.count('\n')==1 and len(raw)<4_000_000,
           'Lean structural export must be one bounded JSON line')
    graph=json.loads(raw)
    closed_keys(graph,{'kind','source_commit','source_blob','declaration','id','abi','command'})
    insist(graph['kind']=='original-structured-source-v1' and
           graph['source_commit']==SOURCE_SHA and
           graph['declaration']==record['fqn'] and
           graph['source_blob']==record['git_blob'] and
           graph['id']==record['id'],'wrong source declaration, blob or protocol')
    abi=graph['abi']
    closed_keys(abi,{'r','s','labels','input','output'})
    insist(all(type(abi[k]) is int for k in abi),'noninteger ABI')
    insist((abi['r'],abi['s'],abi['labels'],abi['input'],abi['output']) ==
           (3,3,TARGET_LABELS,0,0),'unexpected original computeL ABI')
    root=parse_node(graph['command'],3,3,[MAX_NODES])
    insist(root.size+1==TARGET_LABELS and root.entry(1,0)==1,
           'original computeL graph label count or entry mismatch')

    calls=Counter(); kinds=Counter()
    def walk(node):
        kinds[node.kind]+=1
        if node.kind=='call':
            calls[node.size]+=1
            insist(node.size in (11,24), 'unexpected original source callee')
        for child in node.children:walk(child)
    walk(root)
    # 16 increments + one in logSucc, then one logarithm call.
    insist(calls==Counter({11:17,24:1}),
           f'original source no longer matches documented recurrence: {dict(calls)}')
    insist(kinds['skip']==1 and kinds['seq']==18 and kinds['call']==18,
           'unexpected original composition structure')
    return {'labels':TARGET_LABELS,'entry':1,'calls':dict(calls),
            'node_count':sum(kinds.values()),'node_kinds':dict(kinds)},root


def rust_test(raw:str, record:dict)->str:
    """Execute the original source graph bytes through Rust's native JSON loader."""
    digest=hashlib.sha256(raw.encode()).hexdigest()
    return '\n'.join([
        'use std::sync::Arc;',
        'use lean_eth_reference::bit_program::{DeferredProgram, SourceGraphBinding, RunLimits};',
        'use lean_eth_reference::Error;',
        'fn original() -> Result<Arc<DeferredProgram<3,3>>, Error> {',
        '    DeferredProgram::from_original_source_json(include_bytes!("source.json"), SourceGraphBinding {',
        f'        id: {json.dumps(record["id"])},',
        f'        declaration: {json.dumps(record["fqn"])},',
        f'        source_blob: {json.dumps(record["git_blob"])},',
        f'        graph_sha256: "{digest}",',
        '    })',
        '}',
        '#[test]',
        'fn compute_l_original_structural_backend_executes() {',
        '    let p=original().unwrap();',
        '    assert_eq!(p.labels(),212);',
        '    assert_eq!(p.entry(),1);',
        '    for pc in 0..p.labels() { p.instruction_at(pc).unwrap(); }',
        '    for n in 0u32..64 {',
        '        let input=(0..8).map(|i| ((n >> i) & 1) != 0).collect::<Vec<_>>();',
        '        let mut state=p.initial(input);',
        '        p.run(&mut state, RunLimits { max_steps: 250_000, max_stack_bits: 10_000 }).unwrap();',
        '        assert_eq!(state.pc,None,"input={n}");',
        '        let result=state.stacks[0].iter().enumerate().fold(0usize,|v,(i,b)|',
        '            if *b { v | (1usize << i) } else { v });',
        '        let expected=(n+16).ilog2() as usize + 1;',
        '        assert_eq!(result,expected,"input={n}");',
        '    }',
        '}',
    ])+'\n'


def run(upstream:Path,lake:Path,rust_crate:Path,dest:Path,timeout:int):
    pins=ensure_pinned(upstream,lake)
    catalog=discover(upstream,True)['candidates']
    matching=[r for r in catalog if r['fqn']==TARGET]
    insist(len(matching)==1,'pinned original computeL declaration not discovered exactly once')
    record=matching[0]
    insist(blob_hash((upstream/record['file']).read_bytes())==record['git_blob'],
           'original source blob changed')
    with tempfile.TemporaryDirectory(prefix='.compute-l-',dir=lake) as tmp:
        work=Path(tmp)
        probe=work/'Export.lean'
        probe.write_text(probe_source(record),encoding='utf8')
        def execute(*argv):
            p=subprocess.run(argv,cwd=lake,env={**os.environ,'ORIGINAL_MAX_LABELS':'4096'},
                             text=True,capture_output=True,timeout=timeout)
            if p.returncode:
                raise RuntimeError(f'{argv[0]} failed: {p.stderr[-1500:]} {p.stdout[-1500:]}')
            return p.stdout
        execute('lake','-K','maxJobs=2','build',record['module'])
        raw=execute('lake','env','lean',str(probe))
        summary,root=structural_summary(raw,record)
        rust=rust_test(raw,record)
        crate=work/'rust-check'
        (crate/'tests').mkdir(parents=True)
        (crate/'src').mkdir(parents=True)
        (crate/'src/lib.rs').write_text('// Original source structural acceptance\n')
        (crate/'tests/compute_l.rs').write_text(rust)
        (crate/'tests/source.json').write_text(raw)
        (crate/'Cargo.toml').write_text(isolated_cargo_manifest('original-compute-l-check', rust_crate))
        execute('cargo','test','--offline','--manifest-path',str(crate/'Cargo.toml'),'--tests')
        dest.mkdir(parents=True,exist_ok=True)
        atomic_write(dest/'compute-l.graph.json',raw)
        atomic_write(dest/'compute-l.rust.rs',rust)
        summary.update({'kind':'source-elaborated-compute-l-structural-acceptance',
                        'status':'SOURCE_STRUCTURAL_AND_RUST_FUNCTIONAL_CHECK_PASSED',
                        'source_commit':SOURCE_SHA,'source_blob':record['git_blob'],
                        'declaration':TARGET,'pins':pins,
                        'graph_sha256':hashlib.sha256(raw.encode()).hexdigest(),
                        'rust_sha256':hashlib.sha256(rust.encode()).hexdigest(),
                        'limitations':['full original physical table not independently reproduced',
                         'full original Lean state differential not established',
                         'no ETH worst-case complexity claim']})
        atomic_write(dest/'compute-l.receipt.json',json.dumps(summary,indent=2,sort_keys=True)+'\n')
        print('ORIGINAL_COMPUTEL_STRUCTURAL_ACCEPTED',summary['labels'],summary['node_count'],flush=True)
        return summary


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['upstream','lake-root','rust-crate','output-dir']:
        p.add_argument('--'+key,required=True,type=Path)
    p.add_argument('--timeout-seconds',type=int,default=240)
    args=p.parse_args()
    if not (10<=args.timeout_seconds<=1200):p.error('invalid timeout')
    run(args.upstream.resolve(),args.lake_root.resolve(),args.rust_crate.resolve(),
        args.output_dir.resolve(),args.timeout_seconds)

if __name__=='__main__':main()