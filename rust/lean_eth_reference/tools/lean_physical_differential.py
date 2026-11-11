#!/usr/bin/env python3
"""Independently execute pinned Lean BitProgram semantics against Rust.

The physical tables must already have been exported by the original Lean
elaborator. This check extracts *executable definitions* from original
BitProgram.lean and runs Lean 4.34.1 under a minimal Mathlib import closure.
Only the non-executable `Fintype` deriving handler is removed. This is NOT
an import of original OAI modules and does NOT validate the structural graph
exporter. It verifies machine-step semantics using Lean, not a Python oracle.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from export_compiled_batch import ensure_pinned
from extract_compiled_catalog import blob_hash, discover
from verify_source_graph import parse_golden, rust_instr, SOURCE_SHA

RUN_SEEDS = 4
RUN_STEPS = 24
MAX_PROGRAMS = 6
MAX_LABELS = 4096
RUST_CRATE = 'lean_eth_reference'


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def source_semantics(upstream: Path) -> tuple[str, dict[str, str]]:
    path = upstream / 'lean/OAI/Algorithms/SubexponentialSAT/BitProgram.lean'
    raw = path.read_bytes()
    require(len(raw) < 100_000, 'original BitProgram source size unexpected')
    src = raw.decode('utf-8')
    start = src.index('inductive Instr (r s l : ℕ) where')
    end = src.index('abbrev initial {r s l : ℕ}', start)
    executable = src[start:end]
    require(executable.count('def readRegs') == 1 and
            executable.count('def execInstr') == 1 and
            executable.count('abbrev step') == 1,
            'original interpreter source layout changed')
    require(executable.count('deriving DecidableEq, Fintype') == 1,
            'original deriving assumptions changed')
    # Fintype is used by theorem/tactic code, not these executable definitions.
    minimal = executable.replace('deriving DecidableEq, Fintype', 'deriving DecidableEq')
    lean = ('import Mathlib.Data.Fintype.Basic\n'
            'import Mathlib.Logic.Function.Basic\n'
            'import Lean\n'
            'namespace OAI.Algorithms.SubexponentialSAT.BitProgram\n'
            + minimal + '\nend OAI.Algorithms.SubexponentialSAT.BitProgram\n')
    return lean, {
        'bitprogram_git_blob': blob_hash(raw),
        'bitprogram_sha256': hashlib.sha256(raw).hexdigest(),
        'executable_source_span_sha256': hashlib.sha256(executable.encode()).hexdigest(),
        'only_change': 'removed proof-only deriving Fintype',
    }


def lean_instruction(op: tuple[str, tuple[int, ...]]) -> str:
    kind, args = op
    kind = {'not': 'bnot', 'and': 'band', 'or': 'bor', 'xor': 'bxor'}.get(kind, kind)
    parts = list(map(str, args))
    if kind == 'set':
        parts[1] = 'true' if args[1] else 'false'
    return '.' + kind + (' ' + ' '.join(parts) if parts else '')


LEAN_RUNNER = r'''
open Lean OAI.Algorithms.SubexponentialSAT.BitProgram
set_option linter.unnecessarySimpa false

private def bits (xs : List Bool) : String :=
 String.ofList (xs.map fun b => if b then '1' else '0')

private def state {r s l : Nat} (c : Cfg r s l) : String :=
 let pc := match c.pc with | none => "none" | some i => toString i.val
 let regs := bits (List.ofFn c.regs)
 let stackText := String.intercalate "," ((List.ofFn c.«stacks»).map bits)
 s!"{pc}|{regs}|{stackText}"

private def initial {r s l : Nat} (label : Fin l) (seed : Nat) : Cfg r s l := {
 pc := some label
 regs := fun i => ((seed / (2 ^ i.val)) % 2) == 1
 «stacks» := fun i => (List.range ((seed + i.val) % 4)).map
   fun j => ((j + seed + i.val) % 3) == 0
}

private def traceMachine {r s l : Nat} (name : String) (p : Program r s l) : IO Unit := do
 for label in List.finRange l do
  for seed in [:4] do
   let mut cfg := initial label seed
   for index in [:24] do
    match step p cfg with
    | none => break
    | some next =>
      IO.println s!"TRACE|{name}|{label.val}|{seed}|{index}|{state next}"
      cfg := next
'''

RUST_RUNNER = r'''use lean_eth_reference::bit_program::{Config, Instr, Program};
use std::collections::VecDeque;

fn state<const R:usize,const S:usize>(c:&Config<R,S>)->String {
 let pc=c.pc.map_or("none".to_owned(), |x| x.to_string());
 let regs:String=c.regs.iter().map(|b|if *b{'1'}else{'0'}).collect();
 let stacks=c.stacks.iter().map(|s|s.iter().map(|b|if *b{'1'}else{'0'}).collect::<String>()).collect::<Vec<_>>().join(",");
 format!("{pc}|{regs}|{stacks}")
}
fn compare<const R:usize,const S:usize>(p:Program<R,S>,raw:&str,name:&str)->usize {
 let mut count=0;
 let mut seen=std::collections::HashSet::new();
 for line in raw.lines() {
  let words:Vec<&str>=line.split('|').collect();
  assert_eq!(words.len(),8,"bad trace record: {line}");
  assert_eq!(words[0],"TRACE");
  if words[1]!=name {continue;}
  let label=words[2].parse::<usize>().unwrap();
  let seed=words[3].parse::<usize>().unwrap();
  let step=words[4].parse::<usize>().unwrap();
  assert!(label<p.code().len() && seed<4 && step<24);
  seen.insert((label,seed));
  let mut c=p.initial(Vec::<bool>::new());
  c.pc=Some(label);
  c.regs=std::array::from_fn(|i| ((seed/(1usize<<i))%2)==1);
  c.stacks=std::array::from_fn(|i| (0..((seed+i)%4)).map(|j|((j+seed+i)%3)==0).collect::<VecDeque<bool>>());
  for _ in 0..=step {assert!(p.step(&mut c).unwrap(),"premature termination: {line}");}
  assert_eq!(state(&c),words[5..].join("|"),"Lean/Rust transition mismatch: {line}");
  count+=1;
 }
 assert_eq!(seen.len(),p.code().len()*4,"incomplete Lean trace coverage for {name}");
 count
}
'''


def emit_code(programs: list[dict], upstream: Path) -> tuple[str, str]:
    lean, _ = source_semantics(upstream)
    lean += LEAN_RUNNER
    rust = RUST_RUNNER
    calls = []
    for index, p in enumerate(programs):
        r, s, l, entry, input_stack, output_stack = p['abi']
        rows = p['rows']
        original = ', '.join(lean_instruction(op) for op in rows)
        lean += (f'\nprivate def original_{index} : Program {r} {s} {l} := {{\n'
                 f' inputStack := {input_stack}\n outputStack := {output_stack}\n'
                 f' entry := {entry}\n code := fun i => '
                 f'(#[ {original} ] : Array (Instr {r} {s} {l}))[i.val]\' '
                 '(by simpa using i.isLt)\n}\n')
        calls.append(f' traceMachine "{p["id"]}" original_{index}')
        rust += (f'\n#[test]\nfn physical_trace_{index}() {{\n'
                 f' let p=Program::<{r},{s}>::new({input_stack},{output_stack},{entry},vec![\n')
        rust += ''.join(f'  {rust_instr(op)},\n' for op in rows)
        rust += (f' ]).unwrap();\n let n=compare(p,include_str!("../lean-traces.txt"),"{p["id"]}");\n'
                 f' assert!(n>={l}*4);\n eprintln!("LEAN_RUST_MATCH {p["id"]} transitions={{n}}");\n}}\n')
    lean += '\ndef main : IO Unit := do\n' + '\n'.join(calls) + '\n'
    return lean, rust


def run(*argv: str, cwd: Path, timeout: int, env: dict | None = None) -> str:
    r = subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    if r.returncode:
        raise ValueError(f'{argv[0]} failed {r.returncode}: stdout={r.stdout[-2500:]!r}; stderr={r.stderr[-2500:]!r}')
    return r.stdout


def verify_trace(output: str, programs: list[dict]) -> dict[str, int]:
    ids = {p['id']:p for p in programs}
    count = Counter()
    seen: dict[str, set[tuple[int,int,int]]] = {name:set() for name in ids}
    for line in output.splitlines():
        parts = line.split('|')
        require(len(parts)==8 and parts[0]=='TRACE', 'unexpected Lean runtime output')
        ident = parts[1]
        require(ident in ids,'unknown Lean program in trace')
        l = ids[ident]['abi'][2]
        label, seed, step = map(int, parts[2:5])
        require(0<=label<l and 0<=seed<RUN_SEEDS and 0<=step<RUN_STEPS, 'invalid Lean case selector')
        require((label,seed,step) not in seen[ident],'duplicate Lean machine state')
        seen[ident].add((label,seed,step))
        require(parts[5]=='none' or (parts[5].isdigit() and int(parts[5])<l),
                'malformed Lean program counter')
        require(re.fullmatch('[01]*',parts[6]) is not None, 'malformed Lean registers')
        require(len(parts[6])==ids[ident]['abi'][0], 'Lean register count mismatch')
        require(all(re.fullmatch('[01]*',x) is not None for x in parts[7].split(',')),'malformed Lean stacks')
        require(len(parts[7].split(','))==ids[ident]['abi'][1], 'Lean stack count mismatch')
        count[ident] += 1
    # Each label/seed trace must be a contiguous prefix, and halting is final.
    for ident, state_set in seen.items():
        labels = ids[ident]['abi'][2]
        for label in range(labels):
            for seed in range(RUN_SEEDS):
                steps = sorted(k for a, b, k in state_set if a == label and b == seed)
                require(steps == list(range(len(steps))),
                        f'discontinuous Lean transition sequence: {ident} label={label} seed={seed}')
    for p in programs:
        l = p['abi'][2]
        require(set((label,seed,0) for label in range(l) for seed in range(RUN_SEEDS))
                <= seen[p['id']],f'missing initial label coverage: {p["id"]}')
    return dict(count)


def differential(upstream:Path,lake:Path,golden:Path,rust_crate:Path,dest:Path,
                 timeout:int=120) -> dict:
    pins=ensure_pinned(upstream,lake)
    source,span=source_semantics(upstream)
    assert source
    catalog={p['id']:p for p in discover(upstream,True)['candidates']}
    manifest=json.loads((golden/'manifest.json').read_text())
    require(1<=len(manifest)<=MAX_PROGRAMS,'expected bounded set of source programs')
    programs=[]
    for name,expected in sorted(manifest.items()):
        require(name in catalog,'program not found in pinned OAI discovery index')
        rec=catalog[name]
        require(rec['git_blob']==expected['source_blob'] and
                rec['fqn']==expected['declaration'], 'pinned source identity mismatch')
        require(blob_hash((upstream/rec['file']).read_bytes())==rec['git_blob'], 'source blob changed')
        raw=(golden/(name+'.table')).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==expected['sha256'], 'source table digest mismatch')
        abi,rows=parse_golden(raw,name,rec['git_blob'])
        require(abi[2]<=MAX_LABELS, 'source table too large for trace differential')
        programs.append({'id':name,'declaration':rec['fqn'],'source_blob':rec['git_blob'],
                         'table_sha256':expected['sha256'],'abi':abi,'rows':rows})
    lean_code,rust_code=emit_code(programs,upstream)
    with tempfile.TemporaryDirectory(prefix='.physical-diff-',dir=lake) as tmp:
        work=Path(tmp)
        # Files must reside beneath Lake root for the Lean toolchain sandbox.
        (work/'Trace.lean').write_text(lean_code,encoding='utf8')
        env={**os.environ,'ORIGINAL_MAX_LABELS':str(MAX_LABELS)}
        output=run('lake','env','lean','--run',str(work/'Trace.lean'),cwd=lake,timeout=timeout,env=env)
        counts=verify_trace(output,programs)
        dest.mkdir(parents=True,exist_ok=True)
        (dest/'lean-traces.txt').write_text(output,encoding='utf8')
        (dest/'source-semantics.lean').write_text(lean_code,encoding='utf8')
        (dest/'rust-differential.rs').write_text(rust_code,encoding='utf8')
        crate=work/'rust-check'
        (crate/'src').mkdir(parents=True)
        (crate/'tests').mkdir(parents=True)
        (crate/'Cargo.toml').write_text('[package]\nname="lean-physical-differential"\nversion="0.0.0"\nedition="2024"\n\n'
                                          '[dependencies]\nlean_eth_reference={package="lean-eth-reference",path='+json.dumps(str(rust_crate.resolve()))+'}\n')
        (crate/'src/lib.rs').write_text('// Independent Lean state traces\n')
        (crate/'tests/physical.rs').write_text(rust_code)
        (crate/'lean-traces.txt').write_text(output)
        cargo=run('cargo','test','--offline','--manifest-path',str(crate/'Cargo.toml'),'--tests',
                  cwd=crate,timeout=timeout,env=env)
        require('test result: ok.' in cargo,'Rust reported no successful differential tests')
        report={'kind':'source-extracted-Lean-vs-Rust-physical-traces',
                'source_commit':SOURCE_SHA,'pins':pins,
                'source':span,'programs':[{'id':p['id'],'labels':p['abi'][2],
                    'table_sha256':p['table_sha256'],'source_blob':p['source_blob'],
                    'transitions':counts[p['id']]} for p in programs],
                'transition_count':sum(counts.values()),
                'source_semantics_lean_sha256':hashlib.sha256(lean_code.encode()).hexdigest(),
                'trace_sha256':hashlib.sha256(output.encode()).hexdigest(),
                'status':'PASSED_EXTRACTED_ORIGINAL_BITPROGRAM_SEMANTICS',
                'limitations':['original OAI module not imported',
                               'only proof-only Fintype derivation removed',
                               'original source graph not yet exported',
                               'Rust reference step interpreter tested, not complete ETH port']}
        (dest/'report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
        print('LEAN_RUST_PHYSICAL_PARITY',len(programs),'programs',sum(counts.values()),'transitions',flush=True)
        return report


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['upstream','lake-root','golden-dir','rust-crate','output-dir']:
        parser.add_argument('--'+flag,required=True,type=Path)
    parser.add_argument('--timeout-seconds',type=int,default=120)
    a=parser.parse_args()
    if not (10<=a.timeout_seconds<=1200):parser.error('invalid timeout')
    differential(a.upstream.resolve(),a.lake_root.resolve(),a.golden_dir.resolve(),
                 a.rust_crate.resolve(),a.output_dir.resolve(),a.timeout_seconds)

if __name__=='__main__':main()