"""Immutable cases for independent native and propagation benchmark comparisons.

The same operation factory is used in pytest-benchmark and fresh RSS workers.
Each case is verified outside the timed invocation. No search enters production.
"""
from __future__ import annotations
from non_exponential_sudoku.runtime.config import ModeLimits
from dataclasses import dataclass, asdict
from functools import lru_cache
from typing import Callable
from non_exponential_sudoku.core.algebra import Padic,modulus_polynomial
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from reference.real_sudoku_bench import puzzles
from reference.local_support import projected_domains
from reference.sudoku_paper_solver import paper_count


def grid_edges(side):
    return ([(y*side+x,y*side+x+1) for y in range(side) for x in range(side-1)] +
            [(y*side+x,(y+1)*side+x) for y in range(side-1) for x in range(side)])


def get_puzzle(label):
    return next(p for name,p,_ in puzzles() if name==label)


@dataclass(frozen=True)
class StudyCase:
    case_id: str
    variant: str
    parameters: dict
    expected: object
    operation_factory: Callable[[],Callable[[],object]]

    def validate(self):
        answer=self.operation_factory()()
        if answer!=self.expected:
            raise AssertionError(f'{self.case_id}/{self.variant}: {answer!r} != {self.expected!r}')
        return answer


CASES={
    'sparse-grid3':('python','cython'),
    'sparse-grid4':('python','cython'),
    'sparse-grid5':('python','cython'),
    'dense-grid3':('python','cython'),
    'jet-mul':('pairwise','fused'),
    'preprocess-4x4':('matching','incremental','enhanced'),
    'preprocess-9x9':('matching','incremental','enhanced'),
    'preprocess-16x16':('matching','incremental','enhanced'),
    'preprocess-9x9-easy':('matching','incremental','enhanced'),
    'total-9x9-2':('matching','incremental','enhanced'),
    'total-9x9-4':('matching','incremental','enhanced'),
    'total-kernel-9x9-4':('python','cython'),
}

LABELS={
  'preprocess-4x4':'4x4-12-givens-two-solutions',
  'preprocess-9x9':'9x9-77-givens-two-solutions',
  'preprocess-16x16':'16x16-252-givens-two-solutions',
  'preprocess-9x9-easy':'9x9-easy-unique',
  'total-9x9-2':'9x9-77-givens-two-solutions',
  'total-9x9-4':'9x9-73-givens-four-solutions',
  'total-kernel-9x9-4':'9x9-73-givens-four-solutions',
}


def prepare(case_id,variant):
    if case_id not in CASES or variant not in CASES[case_id]:
        raise ValueError(f'Unknown benchmark {case_id!r}/{variant!r}')
    if case_id.startswith(('sparse-grid','dense-grid')):
        side=int(case_id[-1]); edges=grid_edges(side)
        dense=case_id.startswith('dense')
        p=len(edges)+2
        R=Padic(5,modulus_polynomial(5),p)
        modes=[Mode(j,0,0,u,v,1,(),(0,)) for j,(u,v) in enumerate(edges)]
        groups={v for uv in edges for v in uv}
        def child(g,scope,a):
            return R.one if dense or len(set(a))<=1 else R.zero
        expected=R.scalar((1<<len(edges)) if dense else 2)
        def operation_factory():
            def op():
                stats=Counters()
                solver=ModeEliminator(modes,groups,R,child,stats,CapacityError,
                     join_strategy='sparse',order='min_fill',native_sparse=variant=='cython',
                     limits=ModeLimits(max_factor_states=100000, max_live_terms=500000,
                                       max_operations=9_000_000))
                result=solver.run()
                op.last_stats=asdict(stats)
                return result
            return op
        return StudyCase(case_id,variant,{'family':'lattice','side':side,
            'modes':len(edges),'precision':p,'support':'dense' if dense else 'equality'},
            expected,operation_factory)
    if case_id=='jet-mul':
        import native_ring
        q=14;e=6;p=26
        B=Padic(e,modulus_polynomial(e),p)
        a=tuple(tuple((i*127+j*73+k*11+1)%(1<<p) for j in range(e)) for i,k in ((i,i*i) for i in range(q)))
        b=tuple(tuple((i*37+j*41+10)%(1<<p) for j in range(e)) for i in range(q))
        expected=native_ring.jet_mul_pairwise(a,b,e,B.f,B.mask)
        operation_factory=lambda: (lambda: getattr(native_ring,'jet_mul' if variant=='fused' else 'jet_mul_pairwise')(a,b,e,B.f,B.mask))
        return StudyCase(case_id,variant,{'jet_degree':q,'extension_degree':e,'precision':p},expected,operation_factory)
    puzzle=get_puzzle(LABELS[case_id])
    if case_id.startswith('preprocess'):
        # The old algorithm is a reference for supported candidates; no
        # independent Sudoku search is involved in this preprocess microbench.
        expected=projected_domains(puzzle,method='matching')[0]
        def operation_factory():
            def op():
                domains,_,metrics=projected_domains(puzzle,method=variant,return_metrics=True)
                n=puzzle.side
                t=max(1,(n-1).bit_length())
                remaining=0
                for domain in domains:
                    for bit in range(t):
                        possible={((digit-1)>>bit)&1 for digit in range(1,n+1)
                                  if domain&(1<<(digit-1))}
                        if len(possible)==2:
                            remaining+=1
                op.last_metrics={**metrics,'remaining_tensor_wires':remaining,
                                 'total_domain_options':sum(d.bit_count() for d in domains)}
                return domains
            return op
        return StudyCase(case_id,variant,{'side':puzzle.side,'givens':sum(bool(x) for x in puzzle.entries)},expected,operation_factory)
    expected=2 if case_id.endswith('-2') else 4
    def operation_factory():
        def op():
            count,stats=paper_count(puzzle,recovery='jet',
                 propagation='enhanced' if case_id.startswith('total-kernel') else variant,
                 native_sparse=(variant!='python'))
            op.last_stats=stats
            return count
        return op
    return StudyCase(case_id,variant,{'side':puzzle.side,'givens':sum(bool(x) for x in puzzle.entries),
              'metric':'complete_tensor_count'},expected,operation_factory)
