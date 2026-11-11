#!/usr/bin/env python3
"""Validate Lean-elaborated command trees against pinned independently exported tables.

An independent Lean exporter produced the six golden physical tables. This
script checks every physical instruction, then generates Rust *constructors*
for DeferredProgram and executes bounded equivalence tests. It is NOT an
independent Lean/Rust state differential or a completeness claim.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Any

SOURCE_SHA = '4eaee87548250b2682affda7d05d947c05554bae'
KINDS = {
    'halt':'', 'goto':'l','set':'rbl','copy':'rrl','not':'rrl',
    'and':'rrrl','or':'rrrl','xor':'rrrl','branch':'rll',
    'push':'srl','peek':'srrl','pop':'srrl'
}
ATOMS = {name: spec[:-1] for name,spec in KINDS.items() if name not in {'halt','goto','branch'}}
RUST_NAMES = {'halt':'Halt','goto':'Goto','set':'Set','copy':'Copy','not':'Not',
              'and':'And','or':'Or','xor':'Xor','branch':'Branch','push':'Push',
              'peek':'Peek','pop':'Pop'}
FIELDS = {'goto':['next'],'set':['dst','value','next'],
          'copy':['dst','src','next'],'not':['dst','src','next'],
          'and':['dst','left','right','next'],'or':['dst','left','right','next'],
          'xor':['dst','left','right','next'],'branch':['test','yes','no'],
          'push':['stack','src','next'],'peek':['stack','value','present','next'],
          'pop':['stack','value','present','next']}
ATOM_FIELDS={name:fields[:-1] for name,fields in FIELDS.items() if name in ATOMS}
MAX_NODES=8192
MAX_TABLE_LABELS=4096
MAX_SOURCE_LABELS=50000
MAX_INPUT_BYTES=4*1024*1024


def insist(test: bool, message: str):
    if not test: raise ValueError(message)


def number(value: Any, maximum: int, field: str) -> int:
    insist(type(value) is int and 0 <= value <= maximum, f'invalid finite {field}')
    return value


def parse_instr(value: Any, r: int, s: int, l: int, atom=False) -> tuple[str, tuple[int,...]]:
    insist(isinstance(value,str) and len(value)<80 and value.isascii(), 'not a canonical instruction')
    fields=value.split(':')
    kind=fields[0]
    specs=(ATOMS if atom else KINDS)
    insist(kind in specs and len(fields)==len(specs[kind])+1, 'unknown instruction or arity')
    args=[]
    for text,t in zip(fields[1:],specs[kind]):
        insist(bool(re.fullmatch(r'(?:0|[1-9][0-9]*)',text)), 'noncanonical instruction index')
        n=int(text)
        insist(n < {'r':r,'s':s,'l':l,'b':2}[t], 'source instruction operand out of bounds')
        args.append(n)
    return kind,tuple(args)


def fmt(op: tuple[str, tuple[int,...]]) -> str:
    return ':'.join([op[0],*(str(x) for x in op[1])])


def relocated(op: tuple[str, tuple[int,...]], base: int, exit: int):
    name, vals=op
    if name=='halt': return ('goto',(exit,))
    if name=='goto':return ('goto',(base+vals[0],))
    if name=='branch':return ('branch',(vals[0],base+vals[1],base+vals[2]))
    return (name,(*vals[:-1],base+vals[-1]))


class Node:
    def __init__(self, kind: str, size: int, children=(), args=None, table=None):
        self.kind,self.size,self.children,self.args,self.table=kind,size,children,args or {},table

    def entry(self,base:int,exit:int)->int:
        if self.kind=='skip':return exit
        if self.kind in ('atom','if','while'):return base
        if self.kind=='call':return base+self.args['entry']
        if self.kind=='seq':
            a,b=self.children
            return a.entry(base,b.entry(base+a.size,exit))
        raise ValueError('unknown source node')

    def instr(self,base:int,exit:int,pc:int):
        insist(base<=pc<base+self.size,'source node address out of range')
        if self.kind=='atom':return (*self.args['opcode'][0:1],(*self.args['opcode'][1],exit))
        if self.kind=='call':return relocated(self.table[pc-base],base,exit)
        if self.kind=='seq':
            a,b=self.children
            mid=base+a.size
            return a.instr(base,b.entry(mid,exit),pc) if pc<mid else b.instr(mid,exit,pc)
        if self.kind=='if':
            yes,no=self.children
            first=base+1; second=first+yes.size
            if pc==base:return ('branch',(self.args['test'],yes.entry(first,exit),no.entry(second,exit)))
            return yes.instr(first,exit,pc) if pc<second else no.instr(second,exit,pc)
        if self.kind=='while':
            (body,)=self.children
            first=base+1
            if pc==base:return ('branch',(self.args['test'],body.entry(first,base),exit))
            return body.instr(first,base,pc)
        raise ValueError('missing physical node instruction')


def closed_keys(obj:dict[str,Any], keys:set[str]):
    insist(type(obj) is dict and set(obj)==keys, f'noncanonical source node fields: {set(obj) if isinstance(obj,dict) else type(obj)}')


def parse_node(node: Any,r:int,s:int,remaining:list[int],depth=0)->Node:
    insist(depth<=512 and remaining[0]>0,'source graph exceeds bounded graph recursion or node count')
    remaining[0]-=1
    insist(isinstance(node,dict) and isinstance(node.get('kind'),str),'missing source node kind')
    k=node['kind']
    if k=='skip':closed_keys(node,{'kind'});return Node(k,0)
    if k=='atom':
        closed_keys(node,{'kind','opcode'})
        op=parse_instr(node['opcode'],r,s,1,atom=True)
        return Node(k,1,args={'opcode':op})
    if k=='call':
        closed_keys(node,{'kind','program'})
        p=node['program'];closed_keys(p,{'r','s','labels','entry','input','output','code'})
        insist(number(p['r'],256,'r')==r and number(p['s'],4096,'s')==s,'call dimensions differ from source')
        labels=number(p['labels'],MAX_TABLE_LABELS,'call labels');insist(labels>0,'empty source table')
        entry=number(p['entry'],labels,'call entry');insist(entry<labels,'callee entry out of range')
        insist(number(p['input'],s,'input')<s and number(p['output'],s,'output')<s,'callee port out of range')
        insist(isinstance(p['code'],list) and len(p['code'])==labels,'incomplete source call table')
        rows=tuple(parse_instr(op,r,s,labels) for op in p['code'])
        return Node(k,labels,args={'entry':entry,'input':p['input'],'output':p['output']},table=rows)
    if k=='seq':
        closed_keys(node,{'kind','first','second'})
        a=parse_node(node['first'],r,s,remaining,depth+1)
        b=parse_node(node['second'],r,s,remaining,depth+1)
        size=a.size+b.size;insist(size<MAX_SOURCE_LABELS,'composed source exceeds bounded validation labels')
        return Node(k,size,(a,b))
    if k=='if':
        closed_keys(node,{'kind','test','yes','no'})
        test=number(node['test'],r,'branch test');insist(test<r,'branch test out of range')
        a=parse_node(node['yes'],r,s,remaining,depth+1)
        b=parse_node(node['no'],r,s,remaining,depth+1)
        size=a.size+b.size+1;insist(size<MAX_SOURCE_LABELS,'branch source labels exceed bound')
        return Node(k,size,(a,b),{'test':test})
    if k=='while':
        closed_keys(node,{'kind','test','body'})
        test=number(node['test'],r,'while test');insist(test<r,'while test out of range')
        body=parse_node(node['body'],r,s,remaining,depth+1)
        size=body.size+1;insist(size<MAX_SOURCE_LABELS,'loop source labels exceed bound')
        return Node(k,size,(body,),{'test':test})
    raise ValueError(f'unsupported original constructor: {k}')


def parse_golden(raw:bytes,expected_id:str,source_blob:str):
    insist(len(raw)<MAX_INPUT_BYTES and raw.isascii() and raw.endswith(b'\n'),'golden physical table encoding')
    lines=raw.decode('ascii').splitlines()
    insist(lines[0]==f'PIN|{expected_id}|{SOURCE_SHA}|{source_blob}','golden source identity mismatch')
    h=lines[1].split('|');insist(len(h)==8 and h[:2]==['PROGRAM',expected_id],'golden header')
    ints=[]
    for word in h[2:]:
        insist(bool(re.fullmatch(r'(?:0|[1-9][0-9]*)',word)),'golden ABI integer noncanonical')
        ints.append(int(word))
    r,s,l,entry,inp,out=ints
    insist(0<r<=256 and 0<s<=4096 and 0<l<=MAX_TABLE_LABELS and entry<l and inp<s and out<s,'invalid golden ABI')
    insist(len(lines)==l+3 and lines[-1]==f'END|{expected_id}|{l}','incomplete golden table')
    rows=[]
    for i,line in enumerate(lines[2:-1]):
        fields=line.split('|')
        insist(fields[:3]==['CODE',expected_id,str(i)] and len(fields)==4,'golden instruction order')
        rows.append(parse_instr(fields[3],r,s,l))
    return (r,s,l,entry,inp,out),rows


def rust_instr(ins,atom=False):
    name,values=ins
    if name == 'halt' and not atom:
        return 'Instr::Halt'
    fields=(ATOM_FIELDS if atom else FIELDS)[name]
    values=[('true' if value else 'false') if field=='value' else str(value)
            for field,value in zip(fields,values)]
    return f"{'Atom' if atom else 'Instr'}::{RUST_NAMES[name]}" + (
        f" {{ {', '.join(f'{field}: {value}' for field,value in zip(fields,values))} }}" if fields else '')


class RustGenerator:
    def __init__(self,r,s): self.r,self.s,self.lines,self.n=r,s,[],0
    def emit(self,node:Node):
        children=[self.emit(ch) for ch in node.children]
        name=f'n{self.n}';self.n+=1
        match node.kind:
            case 'skip':expr=f'Block::<{self.r},{self.s}>::skip()'
            case 'atom':expr=f"Block::<{self.r},{self.s}>::atom({rust_instr(node.args['opcode'],True)})?"
            case 'seq':expr=f'Block::seq({children[0]}, {children[1]})?'
            case 'if':expr=f"Block::ite({node.args['test']}, {children[0]}, {children[1]})?"
            case 'while':expr=f"Block::while_({node.args['test']}, {children[0]})?"
            case 'call':
                instr=', '.join(rust_instr(row) for row in node.table)
                expr=(f'Block::call(DeferredProgram::table(Program::<{self.r},{self.s}>::new('
                      f"{node.args['input']}, {node.args['output']}, {node.args['entry']}, vec![{instr}])?))")
            case _:raise ValueError('unhandled source node')
        self.lines.append(f'    let {name} = {expr};')
        return name


def generate_test(source:dict,root:Node,golden:list,abi:tuple[int,...])->str:
    r,s,l,entry,inp,out=abi
    emitter=RustGenerator(r,s)
    root_name=emitter.emit(root)
    table=', '.join(rust_instr(row) for row in golden)
    lines=[
        'use std::sync::Arc;',
        'use lean_eth_reference::bit_program::{Atom, Block, DeferredProgram, Instr, Program, RunLimits};',
        f'fn build() -> Result<Arc<DeferredProgram<{r},{s}>>, lean_eth_reference::Error> {{',
        *emitter.lines,
        f'    DeferredProgram::composed({inp}, {out}, {root_name})',
        '}',
        '#[test]',
        'fn original_lean_physical_layout_and_bounded_states() {',
        '    let graph = build().unwrap();',
        f'    let original = Program::<{r},{s}>::new({inp},{out},{entry}, vec![{table}]).unwrap();',
        f'    assert_eq!(graph.labels(), {l});',
        f'    assert_eq!(graph.entry(), {entry});',
        '    for pc in 0..graph.labels() {',
        '        assert_eq!(graph.instruction_at(pc).unwrap(), original.code()[pc], "pc={pc}");',
        '    }',
        '    for bits in [vec![], vec![true], vec![false,true], vec![true,false,true]] {',
        '        let mut a = graph.initial(bits.clone());',
        '        let mut b = original.initial(bits);',
        '        for _ in 0..64 {',
        '            assert_eq!(a.pc,b.pc);',
        '            assert_eq!(a.regs,b.regs);',
        '            assert_eq!(a.stacks,b.stacks);',
        '            assert_eq!(graph.step(&mut a).unwrap(),original.step(&mut b).unwrap());',
        '        }',
        '    }',
        '    let mut bounded = graph.initial([true]);',
        '    assert!(graph.run(&mut bounded, RunLimits { max_steps: 1, max_stack_bits: 1024 }).is_err());',
        '}',
    ]
    return '\n'.join(lines)+'\n'


def validate_and_generate(src:Path, golden_dir:Path, dest:Path, crate:Path, cargo:bool) ->dict:
    insist(src.stat().st_size<=MAX_INPUT_BYTES,'source graph exceeds total byte bound')
    original=src.read_bytes()
    insist(original.endswith(b'\n') and original.count(b'\n')==1,'noncanonical Lean graph stdout')
    parsed=json.loads(original)
    closed_keys(parsed,{'kind','source_commit','source_blob','declaration','id','abi','command'})
    insist(parsed['kind']=='original-structured-source-v1','wrong graph protocol')
    insist(parsed['source_commit']==SOURCE_SHA,'source commit mismatch')
    insist(re.fullmatch('[0-9a-f]{40}',parsed['source_blob']),'source blob malformed')
    insist(re.fullmatch('[a-z0-9_-]{1,255}',parsed['id']),'program ID malformed')
    abi=parsed['abi'];closed_keys(abi,{'r','s','labels','input','output'})
    r=number(abi['r'],256,'r');s=number(abi['s'],4096,'s')
    l=number(abi['labels'],MAX_SOURCE_LABELS,'labels');insist(r>0 and s>0 and l>0,'empty ABI')
    inp=number(abi['input'],s,'input');out=number(abi['output'],s,'output')
    insist(inp<s and out<s,'port out of range')
    root=parse_node(parsed['command'],r,s,[MAX_NODES])
    insist(root.size+1==l,'derived source label count differs from Lean type')
    entry=root.entry(1,0)
    insist(0<=entry<l,'source graph entry outside labels')
    name=parsed['id']
    gold_path=golden_dir/(name+'.table')
    insist(gold_path.is_file(),'not one of the six pinned golden programs')
    hashes=json.loads((golden_dir/'manifest.json').read_text())
    insist(name in hashes,'program absent from golden fixture manifest')
    expect=hashes[name]
    insist(parsed['declaration']==expect['declaration'] and parsed['source_blob']==expect['source_blob'],
           'source declaration/blob differs from golden manifest')
    raw=gold_path.read_bytes()
    insist(hashlib.sha256(raw).hexdigest()==expect['sha256'],'golden source table hash mismatch')
    canonical,rows=parse_golden(raw,name,parsed['source_blob'])
    insist((r,s,l,entry,inp,out)==canonical,'graph program ABI differs from original physical table')
    emitted=[('halt',())]+[root.instr(1,0,pc) for pc in range(1,l)]
    for i,(got,expected) in enumerate(zip(emitted,rows)):
        insist(got==expected,f'exact source physical instruction mismatch at {name}[{i}]: {fmt(got)} vs {fmt(expected)}')
    dest.mkdir(parents=True,exist_ok=True)
    body=generate_test(parsed,root,rows,canonical)
    output=dest/(name+'.rs')
    output.write_text(body)
    receipt={'source_commit':SOURCE_SHA,'source_blob':parsed['source_blob'],
             'declaration':parsed['declaration'],'id':name,
             'graph_sha256':hashlib.sha256(original).hexdigest(),
             'golden_table_sha256':expect['sha256'],
             'generated_rust_sha256':hashlib.sha256(body.encode()).hexdigest(),
             'physical_instructions_compared':l,'status':'EXACT_SOURCE_PHYSICAL_PARITY'}
    (dest/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    if cargo:
        project=dest/('crate-'+name)
        (project/'tests').mkdir(parents=True,exist_ok=True)
        (project/'src').mkdir(parents=True,exist_ok=True)
        (project/'src/lib.rs').write_text('// No semantic SAT oracle\n')
        (project/'tests/source.rs').write_text(body)
        (project/'Cargo.toml').write_text('[package]\nname="original_graph_check"\nversion="0.0.0"\nedition="2024"\n\n'
          '[dependencies]\nlean_eth_reference={package="lean-eth-reference",path='+json.dumps(str(crate.resolve()))+'}\n')
        result=subprocess.run(['cargo','test','--offline','--manifest-path',str(project/'Cargo.toml')],
                              capture_output=True,text=True,timeout=240)
        if result.returncode:
            raise RuntimeError('generated graph Rust test failed: '+result.stderr[-3000:]+' '+result.stdout[-1000:])
    print(f'SOURCE_GRAPH_EXACT {name} labels={l} nodes_probed={MAX_NODES} rust_sha256={receipt["generated_rust_sha256"]}',flush=True)
    return receipt


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--graph',type=Path,required=True)
    p.add_argument('--golden-dir',type=Path,required=True)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--rust-crate',type=Path,required=True)
    p.add_argument('--no-cargo',action='store_true')
    a=p.parse_args()
    validate_and_generate(a.graph,a.golden_dir,a.output_dir,a.rust_crate,not a.no_cargo)
if __name__=='__main__':main()
