#!/usr/bin/env python3
"""Compile and type-check Rust from completed, provenance-bound original Lean tables.

This phase refuses to treat a printed table PIN as authentication: it requires
an SHA-256 receipt emitted by the original Lean export phase, then verifies all
bytes, input dimensions and origin before invoking the Rust code generator.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from export_compiled_batch import SOURCE_SHA, MATHLIB_SHA, verified_receipt


def compile_batch(tables: Path, generated: Path, crate_root: Path, rust_crate: Path,
                  max_labels: int) -> int:
    batch=json.loads((tables/'batch-report.json').read_text())
    proofs=batch.get('exported',[])
    if batch.get('kind')!='original-source-program-export' or not proofs:
        raise ValueError('no source-bound original Lean export receipts')
    pins=batch.get('pins',{})
    if pins.get('source_commit')!=SOURCE_SHA or pins.get('mathlib_commit')!=MATHLIB_SHA \
        or not pins.get('lean','').startswith('Lean (version 4.34.1,'):
        raise ValueError('missing or inconsistent original Lean/Mathlib toolchain receipt')
    generated.mkdir(parents=True,exist_ok=True)
    crate_root.mkdir(parents=True,exist_ok=True)
    (crate_root/'src').mkdir(parents=True,exist_ok=True)
    targets=[]
    for i,record in enumerate(proofs):
        name=record['id']
        blob=record['source_git_blob']
        if record.get('source_commit')!=SOURCE_SHA or record.get('status')!='EXPORTED_FROM_PINNED_LEAN':
            raise ValueError('non-original or incomplete export receipt')
        source=tables/(name+'.table')
        receipt=json.loads((tables/(name+'.receipt.json')).read_text())
        if receipt!=record:
            raise ValueError('batch receipt does not match individual receipt')
        # Require the same source, toolchain, ABI and exporter fingerprint
        # as the resumable compiler; raw tables and PIN lines are insufficient.
        origin = {'id': name, 'module': record['module'],
                  'fqn': record['declaration'], 'git_blob': blob}
        if verified_receipt(tables, origin, max_labels, pins) != record:
            raise ValueError(f'stale or invalid original Lean receipt: {name}')
        rust=generated/(name+'.rs')
        result=subprocess.run(['cargo','run','--quiet','--locked','--offline',
                   '--manifest-path',str(rust_crate/'Cargo.toml'),
                   '--bin','lean-original-codegen','--', name,blob,str(source),str(rust)],
                  text=True,capture_output=True)
        if result.returncode:
            raise RuntimeError(f'original Rust codegen failed for {name}: {result.stderr[-1000:]}')
        # Include only checked Rust files that were generated from a verified table.
        targets.append((name,rust))
        print(f"RUST_GENERATED {name} sha256={hashlib.sha256(rust.read_bytes()).hexdigest()} bytes={rust.stat().st_size}",flush=True)
    lib='// Exact original Lean source compiled into Rust: no generated SAT oracle.\n'
    for index,(name,rust) in enumerate(targets):
        lib+=f'pub mod program_{index} {{ include!({json.dumps(str(rust.resolve()))}); }}\n'
    (crate_root/'src/lib.rs').write_text(lib,encoding='utf-8')
    toml='[package]\nname="pinned_original_lean_batch"\nversion="0.0.0"\nedition="2024"\n\n'
    toml+='[dependencies]\nlean_eth_reference={path='+json.dumps(str(rust_crate.resolve()))+'}\n'
    (crate_root/'Cargo.toml').write_text(toml,encoding='ascii')
    result=subprocess.run(['cargo','check','--offline','--manifest-path',str(crate_root/'Cargo.toml')],
                          text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError('generated original Rust failed type checking: '+result.stderr[-3000:])
    print(f'COMPILED_ORIGINAL_RUST count={len(targets)}; not a Lean/Rust differential proof')
    return len(targets)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tables',type=Path,required=True)
    p.add_argument('--rust-output',type=Path,required=True)
    p.add_argument('--typecheck-crate',type=Path,required=True)
    p.add_argument('--rust-crate',type=Path,required=True)
    p.add_argument('--max-labels',type=int,default=8192)
    args=p.parse_args()
    compile_batch(args.tables.resolve(),args.rust_output.resolve(),
                  args.typecheck_crate.resolve(),args.rust_crate.resolve(),args.max_labels)
if __name__=='__main__':main()
