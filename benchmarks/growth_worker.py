"""One instrumented, resource-limited growth measurement per Linux process.

Run only through benchmarks/growth_study.py or explicitly as a diagnostic.
Correctness is checked against GF(2) rank or closed-form independent counts.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import json
from pathlib import Path
import resource
import sys
import time
import traceback

from .growth_probe import GrowthCollector, RingOperationCounter
from non_exponential_sudoku import (ContractionEngine, ContractorConfig,
    LeafConfig, ModeConfig, ModeLimits, RecoveryConfig, Padic, simple_network)
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.core.modes import Mode, mode_catalog
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.algebra import modulus_polynomial


def lattice_edges(side):
    return ([(y*side+x, y*side+x+1) for y in range(side) for x in range(side-1)] +
            [(y*side+x,(y+1)*side+x) for y in range(side-1) for x in range(side)])


def case(family, size):
    limits = ModeLimits(max_factor_states=4096, max_live_terms=50000,
                        max_operations=2_000_000, max_child_contractions=50000,
                        max_estimated_bytes=96*1024*1024)
    if family in ('parity-cycle','parity-ladder','parity-depth2'):
        from reference.scaling_experiment import parity_network, independent_gf2_count
        kind = 'ladder3' if family == 'parity-ladder' else 'cycle2'
        net = parity_network(kind,size)
        expected, rank = independent_gf2_count(net)
        config = ContractorConfig(
            net.edges, net.edges+3, schedule='micro',
            leaf=LeafConfig(strategy='eliminate'),
            recovery=RecoveryConfig(method='jet', streaming=True),
            mode=ModeConfig(strategy='eliminate',factorization='components',join='adaptive'),
            limits=limits, micro_active_depth=(2 if family=='parity-depth2' else 1))
        engine=ContractionEngine(config)
        return engine.stats, lambda: engine.contract(net)[0], expected, {
            'network_edges': net.edges, 'network_vertices': len(net.left)+len(net.right),
            'independent_GF2_rank':rank,'schedule':'micro','precision_bits':net.edges+3,
            'scope':'full_recursive_contraction',
            'active_depth_limit':2 if family=='parity-depth2' else 1}

    if family == 'sudoku':
        if size not in (4,8):
            raise ValueError('Only canonical 4- and 8-wire Sudoku residuals are available')
        from reference.real_sudoku_bench import puzzles, independent_count_sparse
        from reference.local_support import pin_band_wires
        target=('9x9-77-givens-two-solutions' if size==4 else '9x9-73-givens-four-solutions')
        _,puzzle,declared=next(row for row in puzzles() if row[0]==target)
        expected=independent_count_sparse(puzzle,12)
        if declared!=expected:raise AssertionError('Sudoku reference count discrepancy')
        net,_=pin_band_wires(puzzle)
        if net.edges!=size:raise AssertionError('Sudoku fixture changed wire count')
        config=ContractorConfig(net.edges,net.edges+3,schedule='micro',
            leaf=LeafConfig(strategy='eliminate'),
            recovery=RecoveryConfig(method='jet',streaming=True),
            mode=ModeConfig(strategy='eliminate',factorization='components',join='adaptive'),
            limits=limits)
        engine=ContractionEngine(config)
        return engine.stats,lambda:engine.contract(net)[0],expected,{
            'network_edges':net.edges,'network_vertices':len(net.left)+len(net.right),
            'puzzle':target,'schedule':'micro','precision_bits':net.edges+3,
            'scope':'full_recursive_contraction','oracle':'independent-Sudoku-search'}

    if family == 'crossing':
        net = simple_network(
            size, [([i], {(0,):1,(1,):1}) for i in range(size)],
            [([i], {(0,):1,(1,):1}) for i in range(size)])
        p=size+5
        packed=pack(net,64,2,(tuple((0,0) for _ in range(size)),
                              tuple((1,0) for _ in range(size))))
        config=ContractorConfig(size,p,schedule='geometry64',
            mode=ModeConfig(strategy='eliminate',factorization='components',
                            order='min_fill',join='adaptive'),
            leaf=LeafConfig(strategy='eliminate'),limits=limits)
        engine=ContractionEngine(config)
        ring=Padic(engine.e,engine.f,p)
        modes=mode_catalog(net,packed,1,p)
        return engine.stats,lambda:engine.evaluate_deformation(
            net,packed,modes,1,ring.basis(3),ring,0)[0],2**size,{
            'network_edges':size,'network_vertices':2*size,
            'schedule':'geometry64','precision_bits':p,
            'scope':'one_real_deformation_not_complete_recovery',
            'mode_descriptors':len(modes)}

    if family in ('grid-sparse','grid-dense','parallel-dense'):
        edges=([(0,1)]*size if family=='parallel-dense' else lattice_edges(size))
        n=len(edges)
        p=n+3
        ring=Padic(5,modulus_polynomial(5),p)
        modes=[Mode(j,0,0,u,v,1,(),(0,)) for j,(u,v) in enumerate(edges)]
        groups={g for m in modes for g in (m.source,m.target)}
        stats=Counters()
        sparse=(family=='grid-sparse')
        def factor(g,sc,b):
            return (ring.one if len(set(b))<=1 else ring.zero) if sparse else ring.one
        def run():
            value=ModeEliminator(
                modes,groups,ring,factor,stats,CapacityError,
                order='min_fill',join_strategy='sparse' if sparse else 'adaptive',
                limits=limits).run()
            if any(value[k] for k in range(1,ring.e)):
                raise AssertionError('unexpected non-scalar grid contraction')
            return value[0]
        return stats,run,2 if sparse else 2**n,{
            'network_edges':n,'network_vertices':2 if family=='parallel-dense' else size**2,
            'scope':'mode_elimination_only_synthetic_local_factors',
            'precision_bits':p,'schedule':'synthetic',
            'oracle':'all-edge-equality-connected' if sparse else 'unconstrained-binary-edge-modes'}
    raise ValueError(f'Unknown family {family!r}')


def measure(family,size):
    stats, operation, expected, parameters = case(family,size)
    probe=GrowthCollector()
    stats.growth_probe=probe
    status='completed'
    result=None
    error=None
    t0=time.perf_counter()
    with RingOperationCounter() as arithmetic:
        try:
            result=operation()
            if result != expected:
                status='incorrect'
                error=f'Expected {expected}, obtained {result}'
        except CapacityError as exc:
            status='capacity_refused'
            error=str(exc)
        except BaseException as exc:
            status='error'
            error=f'{type(exc).__name__}: {exc}'
    elapsed=time.perf_counter()-t0
    return {
        'schema_version':'1.0.0', 'case_id':f'{family}-{size}',
        'family':family,'size':size,'parameters':parameters,
        'status':status, 'expected_exact_count':str(expected),
        'observed_exact_count':str(result) if result is not None else None,
        'error':error,
        'runtime':{'instrumented_wall_seconds':elapsed,
                   'peak_process_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024},
        'structural':probe.summary(),
        'ring_arithmetic':arithmetic.summary(),
        'solver_counters':asdict(stats),
        'elimination_invocations':probe.records,
    }


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('family',choices=['parity-cycle','parity-ladder','parity-depth2','sudoku','crossing','grid-sparse','grid-dense','parallel-dense'])
    parser.add_argument('size',type=int)
    parser.add_argument('--memory-mib',type=int,default=768)
    args=parser.parse_args()
    if args.memory_mib:
        limit=args.memory_mib*1024*1024
        resource.setrlimit(resource.RLIMIT_AS,(limit,limit))
    try:
        row=measure(args.family,args.size)
    except BaseException as exc:
        row={'schema_version':'1.0.0','case_id':f'{args.family}-{args.size}',
             'family':args.family,'size':args.size,'status':'error',
             'error':f'{type(exc).__name__}: {exc}',
             'traceback':traceback.format_exc(limit=5)}
    sys.stdout.write(json.dumps(row,sort_keys=True)+'\n')
    return 0 if row['status'] in ('completed','capacity_refused') else 1

if __name__=='__main__':raise SystemExit(main())
