"""Exact native-vs-Python kernel comparisons, including refusal semantics."""
from __future__ import annotations
from non_exponential_sudoku.runtime.config import ModeLimits
from dataclasses import asdict
from itertools import product
import random
import pytest
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.statistics import Counters
from tests.support.mode_factors import synthetic_modes

pytestmark=[pytest.mark.checkpoint, pytest.mark.requires_native]


def run_sparse(native, *, factor_limit=4096, op_limit=200000):
    R=Padic(5,modulus_polynomial(5),8)
    pairs=[(0,1),(1,2),(2,0),(2,3),(3,4),(4,2)]
    modes=synthetic_modes(pairs,R.p)
    def child(g,scope,assignment):
        return R.scalar((2+sum(assignment)+g)%3) if sum(assignment)<=2 else R.zero
    stats=Counters()
    engine=ModeEliminator(modes,{g for e in pairs for g in e},R,child,stats,CapacityError,
                          join_strategy='sparse',order='min_fill',native_sparse=native,
                          limits=ModeLimits(max_factor_states=factor_limit,max_operations=op_limit))
    try:
        answer=engine.run()
        return ('ok',answer,asdict(stats),engine.budget.operations)
    except CapacityError as exc:
        return ('capacity',str(exc),asdict(stats),engine.budget.operations)


def test_native_matches_reference_counts_and_full_work_counters():
    pytest.importorskip('native_sparse')
    assert run_sparse(True)==run_sparse(False)


@pytest.mark.parametrize('max_operations', [5,20,100])
def test_native_matches_reference_capacity_and_work(max_operations):
    pytest.importorskip('native_sparse')
    assert run_sparse(True,op_limit=max_operations)==run_sparse(False,op_limit=max_operations)


@pytest.mark.parametrize('e,p,q',[(2,2,1),(3,7,3),(4,15,5),(6,30,6)])
def test_fused_native_jet_multiply_matches_pairwise_and_python(e,p,q):
    nr=pytest.importorskip('native_ring')
    rng=random.Random(e*10000+p*10+q)
    B=Padic(e,modulus_polynomial(e),p)
    R=JetRing(B,q)
    for _ in range(12):
        a=tuple(tuple(rng.randrange(1<<p) for _ in range(e)) for _ in range(q))
        b=tuple(tuple(rng.randrange(1<<p) for _ in range(e)) for _ in range(q))
        actual=nr.jet_mul(a,b,e,B.f,B.mask)
        assert actual==nr.jet_mul_pairwise(a,b,e,B.f,B.mask)
        assert actual==R.mul(a,b)
