#!/usr/bin/env python3
"""Exact Sudoku counting/witnesses through OpenAI's Appendix-D recursion.

No SAT, DFS Sudoku solver, or external counting oracle is used for results.
A polynomial-time support filter removes forced bit wires, and each count
comes exclusively from the paper-specific tensor contractor (or its base
case). The default experimental schedule uses the exact recursion identity
with tractable finite parameters, not the theorem's asymptotic schedule.
"""
from __future__ import annotations
from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig, RecursionConfig
import argparse
import json
from dataclasses import asdict
from pathlib import Path
from non_exponential_sudoku.sudoku.three_cnf import DIGITS, Puzzle
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.local_support import LocalContradiction, projected_domains, pin_band_wires


def paper_count(puzzle:Puzzle,mode='micro',leaf_limit=18,leaf_strategy='eliminate',recovery='interpolate',active_depth=1,adaptive_leaf_limit=0,mode_strategy='eliminate',
                mode_factorization='components',mode_order='min_fill',mode_join='adaptive',propagation='enhanced',native_sparse=True,recursion=None):
    try:
        net,info=pin_band_wires(puzzle,propagation=propagation)
    except LocalContradiction as e:
        return 0,{'contradiction':str(e),'remaining_wires':0,'recursive_calls':0,'active_levels':0}
    contractor=ContractionEngine(ContractorConfig(max(1,net.edges), net.edges+1, schedule=mode, mode=ModeConfig(strategy=mode_strategy, factorization=mode_factorization, order=mode_order, join=mode_join, native_sparse=native_sparse), recovery=RecoveryConfig(method=recovery), leaf=LeafConfig(limit=leaf_limit, strategy=leaf_strategy, adaptive_limit=adaptive_leaf_limit), micro_active_depth=active_depth,
              recursion=recursion if recursion is not None else RecursionConfig()))
    value=contractor.contract(net)
    if any(value[1:]):raise AssertionError('Unexpected non-integer coefficient')
    return value[0],{**info,**asdict(contractor.stats),
                     'active_levels':len(contractor.stats.active_depth_counts)}


def solve(puzzle:Puzzle,mode='micro',leaf_limit=18,leaf_strategy='eliminate',
          max_count_queries=200,recovery='interpolate',active_depth=1,adaptive_leaf_limit=0,
          mode_strategy='eliminate',mode_factorization='components',mode_order='min_fill',mode_join='adaptive',propagation='enhanced',native_sparse=True,recursion=None):
    count,root=paper_count(puzzle,mode,leaf_limit,leaf_strategy,recovery,active_depth,adaptive_leaf_limit,
                          mode_strategy,mode_factorization,mode_order,mode_join,propagation=propagation,native_sparse=native_sparse,recursion=recursion)
    result={'status':'solved' if count else 'unsatisfiable','box':puzzle.b,
            'side':puzzle.side,'count':count,'root':root,'schedule':mode,
            'literal_theorem_schedule':mode=='paper',
            'theorem_admissible_active_regime_tested':False,
            'queries':1}
    if not count:return result
    assignments=list(puzzle.entries)
    while any(x==0 for x in assignments):
        temporary=Puzzle(puzzle.b,tuple(assignments))
        domains,rounds=projected_domains(temporary,method=propagation)
        # Choose the first unresolved cell with more than one supported digit.
        free=[k for k,v in enumerate(assignments) if v==0]
        forced=[k for k in free if domains[k].bit_count()==1]
        if forced:
            for k in forced:assignments[k]=domains[k].bit_length()
            continue
        target=min(free,key=lambda k:(domains[k].bit_count(),k))
        found=False
        for digit in range(1,puzzle.side+1):
            if not (domains[target] & (1<<(digit-1))):continue
            if result['queries']>=max_count_queries:
                raise CapacityError('Solution self-reduction query cap reached')
            attempt=assignments.copy();attempt[target]=digit
            choices,_=paper_count(Puzzle(puzzle.b,tuple(attempt)),mode,
                                  leaf_limit,leaf_strategy,recovery,active_depth,adaptive_leaf_limit,
                                  mode_strategy,mode_factorization,mode_order,mode_join,propagation=propagation,native_sparse=native_sparse,recursion=recursion)
            result['queries']+=1
            if choices:
                assignments[target]=digit
                found=True
                break
        if not found:raise AssertionError('Positive count but no solution extension')
    solution=tuple(assignments)
    if not puzzle.valid_solution(solution):raise AssertionError('Invalid solution witness')
    result['solution']=''.join(DIGITS[d-1] for d in solution)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('puzzle',help='Puzzle as text with dots for blanks, or @filename')
    ap.add_argument('--box',type=int,default=3)
    ap.add_argument('--schedule',choices=('micro','geometry64','paper'),default='micro')
    ap.add_argument('--leaf-limit',type=int,default=18)
    ap.add_argument('--leaf-strategy',choices=('eliminate','enumerate'),default='eliminate')
    ap.add_argument('--count-only',action='store_true')
    ap.add_argument('--recovery',choices=('interpolate','jet'),default='interpolate',
                    help='Experimental Taylor-jet recovery, including nested active micro levels')
    ap.add_argument('--mode-strategy',choices=('eliminate','enumerate'),default='eliminate',
                    help='Exact mode-graph variable elimination or reference enumeration')
    ap.add_argument('--mode-factorization',choices=('components','whole'),default='components',
                    help='Exact connected-packet component splitting or whole-group reference')
    ap.add_argument('--mode-order',choices=('min_fill','min_states'),default='min_fill',
                    help='Domain-weighted min-fill or minimum immediate factor size')
    ap.add_argument('--python-sparse', action='store_true',
                    help='Use the Python sparse-elimination reference kernel')
    ap.add_argument('--propagation',choices=('matching','incremental','enhanced'),default='enhanced',
                    help='Polynomial exact-cover support reduction with optional matching projection')
    ap.add_argument('--mode-join',choices=('adaptive','enumerate','sparse'),default='adaptive',
                    help='Sparse nonzero-support natural joins, separator scans, or adaptive selection')
    ap.add_argument('--active-depth',type=int,default=1,
                    help='Number of experimental active recursion levels. Two levels may be much slower.')
    ap.add_argument('--adaptive-leaf-limit',type=int,default=0,
                    help='Optional exact terminal cutoff for small nonroot experimental children')
    args=ap.parse_args()
    text=Path(args.puzzle[1:]).read_text() if args.puzzle.startswith('@') else args.puzzle
    puzzle=Puzzle.from_text(text,args.box)
    try:
        if args.count_only:
            count,stats=paper_count(puzzle,args.schedule,args.leaf_limit,args.leaf_strategy,args.recovery,args.active_depth,args.adaptive_leaf_limit,args.mode_strategy,
                                    args.mode_factorization,args.mode_order,args.mode_join,propagation=args.propagation,native_sparse=not args.python_sparse)
            result={'count':count,'stats':stats,'schedule':args.schedule}
        else:
            result=solve(puzzle,args.schedule,args.leaf_limit,args.leaf_strategy,
                         recovery=args.recovery,active_depth=args.active_depth,
                         adaptive_leaf_limit=args.adaptive_leaf_limit,mode_strategy=args.mode_strategy,
                         mode_factorization=args.mode_factorization,mode_order=args.mode_order,
                         mode_join=args.mode_join,propagation=args.propagation,native_sparse=not args.python_sparse)
    except CapacityError as e:
        result={'status':'capacity_refusal','reason':str(e),'schedule':args.schedule}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
