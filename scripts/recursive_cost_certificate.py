"""Emit instance-level recurrence evidence and explicit unresolved proof obligations.

An empirical trace or a bounded resource budget is NOT a proof of a
subexponential upper bound. The complete fallback is an explicit 2**M direct
sum. Oracle internal costs must be bounded separately for any time theorem.
"""
from __future__ import annotations
from dataclasses import asdict
import json,argparse
from pathlib import Path
from benchmarks.recursive_cases import get_case,IDS,VARIANTS

ROOT=Path(__file__).resolve().parents[1]


def direct_bound(net):
    m=net.edges
    v=len(net.left)+len(net.right)
    leaves=1<<m
    return {'wire_count_M':m,'network_vertices':v,'wire_assignments_exact':str(leaves),
        'oracle_calls_at_most':str(leaves*v),
        'outer_ring_multiplications_at_most':str(leaves*v),
        'outer_ring_additions_exact':str(leaves),
        'external_oracle_internal_cost':'UNBOUNDED_BY_THIS_CERTIFICATE',
        'asymptotic_time':'O(2**M * (V + oracle_work(M)))',
        'execution_path':'explicit opt-in contract_complete; no leaf size refusal',
        'status':'EXHAUSTIVE_EXPONENTIAL_REFERENCE_NOT_APPENDIX_D'}


def measured(case_id,variant):
    case=get_case(case_id,variant)
    value,stats=case.validate()
    return {'case':case_id,'variant':variant,'actual':value,'expected':case.expected,
        'parameters':case.parameters,'recursion_counters':asdict(stats),
        'base_case_reference_bound':direct_bound(case.network),
        'status':'EXACT_FINITE_INSTANCE_ONLY'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--cases',default='parity-2wire,sudoku-4wire,sudoku-8wire,nested-2wire,crossing-4wire');p.add_argument('--variant',default='memo',choices=VARIANTS);p.add_argument('--output',type=Path,default=ROOT/'benchmark-results/recursion/cost_certificate.json');args=p.parse_args()
    data={'schema_version':'1.0','result':'INCOMPLETE_THEOREM_CERTIFICATE',
        'target_binary_wires':'2**o(M) total exact arithmetic bit operations on arbitrary M-wire networks',
        'stronger_sudoku_target':'2**o(N) in Sudoku cells N, subject to a specified encoding and input family',
        'desired_appendix_d_recurrence':
          'T(d,M,p) <= planning_and_recovery(d,M,p) + sum_(t, local factor f, admissible beta) T(d+1,M_child(f),p_child) + factor_and_coefficient_work(d,M,p)',
        'known_missing_uniform_bounds':[
          'explicit bound for total admissible mode tuples and local factor states on every input',
          'summable bound on recursively evaluated child factors, including repeated values',
          'factor-elimination width and polynomial/jet coefficient arithmetic bit complexity',
          'precision escalation and Hermite coefficient-recovery work',
          'completion of the paper schedule without fixed finite resource refusals',
          'a recurrence solution with exponent o(M) valid for arbitrary inputs'],
        'mathematical_notes':[
          'Compiling child plans and caching packet entries reduce constants, not the recurrence exponent.',
          'Explicit contract_complete avoids solver capacity guards but has 2**M assignments.',
          'Measured counters are not an operation-level upper bound for native arbitrary-precision arithmetic.'
        ],'instances':[]}
    for case_id in args.cases.split(','):
        data['instances'].append(measured(case_id,args.variant))
    # These are actual unresolved Sudoku instances, not pre-pinned small
    # residual networks. Their bounded-paper outcomes must not be called solved.
    from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig
    from non_exponential_sudoku.sudoku.three_cnf import Puzzle
    from non_exponential_sudoku.sudoku.encoding import sudoku_network
    from non_exponential_sudoku.runtime.budget import CapacityError
    data['unresolved_stress']=[]
    for box in (2,3):
        puzzle=Puzzle.from_text('.'*(box**4),box)
        net=sudoku_network(puzzle)
        engine=ContractionEngine(ContractorConfig(max(1,net.edges),max(1,net.edges)+1,
                  schedule='paper',leaf=LeafConfig(limit=18)))
        try:
            result=engine.contract(net)
        except CapacityError as exc:
            record={'status':'EXPLICIT_CAPACITY_REFUSAL','message':str(exc)}
        else:
            record={'status':'EXACT_COMPLETION','value':str(result[0])}
        data['unresolved_stress'].append({'box_side':box,'side':box*box,
                'givens':0,'network_edges':net.edges,**record,
                'unbounded_fallback_outer_cost':direct_bound(net)})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(args.output)
if __name__=='__main__':main()
