#!/usr/bin/env python3
"""Actual 4x4/9x9/16x16 Sudoku puzzles, no witness-assisted conditioning.

The input is only the givens. Matching-based local-support reductions
substitute mathematically forced wires, then the unchanged Appendix-D
contractor counts every remaining completion. A capacity refusal means the
real algorithm is still intractable for that instance.
"""
from __future__ import annotations
from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
import argparse
import json
import time
from dataclasses import asdict
from pathlib import Path
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.local_support import LocalContradiction, pin_band_wires
from reference.generalized_bench import canonical_solution

REFERENCE_9=('534678912''672195348''198342567''859761423''426853791'
             '713924856''961537284''287419635''345286179')
EASY_9=('53..7....''6..195...''.98....6.''8...6...3''4..8.3..1'
        '7...2...6''.6....28.''...419..5''....8..79')
HARD_9=('1....7.9..3..2...8..96..5....53..9...1..8...26....4...3......1..4......7..7...3..')


def puzzles():
    for b,ref,cells,label in (
        (2,None,[0,2,4,6],'4x4-12-givens-two-solutions'),
        (3,tuple(map(int,REFERENCE_9)),[32,35,41,44],
         '9x9-77-givens-two-solutions'),
        (4,None,[0,8,32,40],'16x16-252-givens-two-solutions')):
        solved=ref or canonical_solution(b)
        givens=list(solved)
        for c in cells:givens[c]=0
        puzzle=Puzzle(b,tuple(givens))
        yield label,puzzle,2
    # Two disjoint intercalates produce four independent completions.
    x=list(canonical_solution(2))
    for cell in (0,2,4,6,8,10,12,14):x[cell]=0
    yield '4x4-8-givens-four-solutions',Puzzle(2,tuple(x)),4
    x=list(map(int,REFERENCE_9))
    for cell in (16,17,61,62,32,35,41,44):x[cell]=0
    yield '9x9-73-givens-four-solutions',Puzzle(3,tuple(x)),4
    yield '9x9-easy-unique',Puzzle.from_text(EASY_9,3),1
    yield '9x9-hard-unique',Puzzle.from_text(HARD_9,3),1
    yield '9x9-contradictory-clues',Puzzle.from_text('55'+EASY_9[2:],3),0


def independent_count_sparse(puzzle:Puzzle,max_blanks:int=8):
    """Reference enumerator using only Sudoku DIGIT domains, not tensors.

    Restricted to <=8 blank cells by construction. This is benchmark-only,
    not an implementation path for the requested recursive contractor.
    """
    from itertools import product
    unknown=[i for i,val in enumerate(puzzle.entries) if not val]
    if len(unknown)>max_blanks:return None
    n=puzzle.side
    by_cell=[[] for _ in range(n*n)]
    for unit in puzzle.units():
        for cell in unit:by_cell[cell].append(unit)
    domains=[]
    for cell in unknown:
        used={puzzle.entries[j] for unit in by_cell[cell] for j in unit
              if puzzle.entries[j]}
        domains.append(tuple(d for d in range(1,n+1) if d not in used))
    count=0
    for vals in product(*domains):
        candidate=list(puzzle.entries)
        for cell,val in zip(unknown,vals):candidate[cell]=val
        if puzzle.valid_solution(tuple(candidate)):count+=1
    return count


def benchmark(name,puzzle,expected,mode='micro',leaf_limit=18,
              leaf_strategy='eliminate',max_mode_tuples=20000):
    start=time.perf_counter()
    oracle_count=independent_count_sparse(puzzle)
    if oracle_count is not None and oracle_count!=expected:
        raise AssertionError((name,oracle_count,expected))
    result={'independent_digit_count':oracle_count,'fixture':name,'box':puzzle.b,'side':puzzle.side,
            'givens':sum(v!=0 for v in puzzle.entries),'expected_count':expected,
            'mode':mode,'leaf_strategy':leaf_strategy}
    try:
        net,info=pin_band_wires(puzzle)
        result.update(info)
        count_bits=net.edges+1
        contractor=ContractionEngine(ContractorConfig(max(1,net.edges), count_bits, schedule=mode, mode=ModeConfig(max_tuples=max_mode_tuples), leaf=LeafConfig(limit=leaf_limit, strategy=leaf_strategy)))
        value=contractor.contract(net)
        result['actual_count']=value[0]
        result['status']='verified' if value[0]==expected and all(x==0 for x in value[1:]) else 'mismatch'
        result['stats']=asdict(contractor.stats)
    except LocalContradiction as ex:
        result.update({'actual_count':0,'status':'verified' if expected==0 else 'mismatch',
                       'reason':str(ex)})
    except CapacityError as ex:
        result.update({'actual_count':None,'status':'capacity_refusal',
                       'reason':str(ex),'stats':asdict(contractor.stats)})
    result['seconds']=round(time.perf_counter()-start,6)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture',action='append')
    parser.add_argument('--schedule',choices=('paper','micro','geometry64'),default='micro')
    parser.add_argument('--leaf-strategy',choices=('enumerate','eliminate'),default='eliminate')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    report=[]
    for name,puzzle,expected in puzzles():
        if args.fixture and name not in args.fixture:continue
        value=benchmark(name,puzzle,expected,args.schedule,
                        leaf_strategy=args.leaf_strategy)
        print(json.dumps(value),flush=True)
        report.append(value)
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
