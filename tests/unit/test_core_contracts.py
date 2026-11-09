"""Fast, parameterized mathematics: distinct oracles and independent oracle checks."""
from dataclasses import FrozenInstanceError
from itertools import product
import random

import pytest
from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig,
)
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.modes import Mode, weighted_tuples
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.contraction.planning import build_factorization_plan
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.scaling_experiment import parity_network, independent_count
from tests.fixtures.cases import PARITY_CASES
from tests.support.mode_factors import (
    synthetic_modes, reference_factor_sum, dp_sum,
    exhaustive_weighted_assignments,
)

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize('degree,precision', [
    (2, 3), (2, 11), (3, 7), (5, 9),
], ids=['2-3', '2-11', '3-7', '5-9'])
def test_exact_ring_identities(degree, precision):
    ring = Padic(degree, modulus_polynomial(degree), precision)
    rng = random.Random(1017 + degree*100 + precision)
    for _ in range(6):
        a,b,c = [tuple(rng.randrange(1 << precision) for _ in range(degree))
                   for _ in range(3)]
        assert ring.mul(a, ring.add(b, c)) == ring.add(ring.mul(a,b), ring.mul(a,c))
        assert ring.mul(a,b) == ring.mul(b,a)
        assert ring.add(a, ring.neg(a)) == ring.zero
        assert ring.mul(a,ring.one) == a


@pytest.mark.parametrize('outer,inner', [(4,2), (5,3), (7,4)])
def test_truncated_jet_multiplication(outer, inner):
    base = Padic(3, modulus_polynomial(3), 7)
    large,small = JetRing(base, outer),JetRing(base,inner)
    rng = random.Random(outer*19 + inner)
    for _ in range(5):
        a,b = [tuple(tuple(rng.randrange(128) for _ in range(base.e))
                     for _ in range(outer)) for _ in (0,1)]
        assert large.mul(a,b)[:inner] == small.mul(a[:inner],b[:inner])


@pytest.mark.parametrize('precision', [2, 3, 4, 5])
def test_mode_weight_tuple_generator_matches_independent_product(precision):
    # This deliberately does NOT use the production enumeration as the oracle.
    modes=[Mode(i,0,0,i,i+1,(i%2)+1,(),(0,)) for i in range(3)]
    assert list(weighted_tuples(modes,precision)) == list(
        exhaustive_weighted_assignments(modes,precision))


@pytest.mark.parametrize('pairs', [
    ((0,1),), ((0,1),(1,2)), ((0,1),(1,2),(2,0)),
    ((0,1),(2,3),(4,5)),
], ids=['edge', 'path', 'cycle', 'disconnected'])
@pytest.mark.parametrize('join', ['enumerate', 'sparse', 'adaptive'])
def test_factor_elimination_equals_independent_oracle(pairs, join):
    ring=Padic(3,modulus_polynomial(3),5)
    modes=synthetic_modes(pairs,ring.p)
    scopes={g:tuple(j for j,m in enumerate(modes) if g in (m.source,m.target))
            for pair in pairs for g in pair}
    # A sparse factor with nontrivial, deterministic coefficients.
    tables={g:{bits:ring.scalar((sum(bits)+g*3+1)%5 if not (g%2 and sum(bits)>1) else 0)
               for bits in product((0,1),repeat=len(scope))}
            for g,scope in scopes.items()}
    evaluate=lambda g,scope,bits: tables[g][bits]
    expected=reference_factor_sum(modes,ring,evaluate)
    actual,stats=dp_sum(modes,ring,evaluate,join_strategy=join)
    assert actual == expected
    assert stats.mode_dp_eliminations == len(modes)


@pytest.mark.parametrize('case', PARITY_CASES, ids=lambda case:case.id)
def test_independent_parity_count(case):
    net=parity_network(case.kind, case.parameter)
    count,rank=independent_count(case.kind,case.parameter)
    assert count==case.expected
    assert count==1 << (net.edges-rank)
    ring=Padic(2,modulus_polynomial(2),8)
    if net.edges<=6:
        assert net.direct(ring,limit=6)[0]==case.expected


@pytest.mark.parametrize('left,right,expected', [
    ({(0,):1, (1,):1},{(0,):1, (1,):1},2),
    ({(1,):1},{(0,):1},0),
    ({(0,):1},{(0,):1},1),
], ids=['two','unsatisfiable','one'])
def test_small_recursive_count_against_truth_table(left,right,expected):
    net=simple_network(1,[([0],left)],[([0],right)])
    assert expected==sum(left.get((i,),0)*right.get((i,),0) for i in (0,1))
    engine=ContractionEngine(ContractorConfig(
        1,4,schedule='micro',root_labels=(((0,),),((1,),))))
    assert engine.contract(net)[0]==expected


def test_component_plan_is_pure_and_complete():
    net=simple_network(3,[([i],{(0,):1,(1,):1}) for i in range(3)],
                       [([i],{(0,):1,(1,):1}) for i in range(3)])
    packing=pack(net,64,2,(tuple((0,0) for _ in range(3)),
                            tuple((1,0) for _ in range(3))))
    modes=mode_catalog(net,packing,1,6)
    occupied={0,1}
    affected={g:tuple(i for i,m in enumerate(modes)
                      if g in (m.source,m.target)) for g in occupied}
    plan=build_factorization_plan(net,packing,modes,0,occupied,affected)
    assert plan.max_arity_after < plan.max_arity_before
    for group in occupied:
        flattened=[j for spec in plan.factors if spec.group==group for j in spec.mode_indices]
        assert sorted(flattened)==sorted(affected[group])


def test_capacity_refusal_is_explicit():
    ring=Padic(3,modulus_polynomial(3),7)
    modes=synthetic_modes([(0,1)]*4,ring.p)
    with pytest.raises(CapacityError,match='limit'):
        dp_sum(modes,ring,lambda *args:ring.one,max_factor_states=3)


def test_immutable_config_rejects_unsupported_paper_jet():
    config=ContractorConfig(2,5,schedule='micro')
    with pytest.raises(FrozenInstanceError):
        config.precision=3
    with pytest.raises(ValueError,match='Jet recovery'):
        ContractorConfig(2,5,schedule='paper',recovery=RecoveryConfig(method='jet'))
    with pytest.raises(ValueError):
        ModeLimits(max_operations=0)
    with pytest.raises(ValueError):
        ContractorConfig(2,5,schedule='micro',mode=ModeConfig(join='unknown'))


def test_no_flat_compatibility_imports():
    from importlib.util import find_spec
    for module in ('recursive_contractor','jet_ring','mode_elimination',
                   'packet_lazy','streaming_hermite','sudoku_3cnf'):
        assert find_spec(module) is None, module


def test_config_is_keyword_order_independent():
    from non_exponential_sudoku import PacketConfig,LeafConfig
    a=ContractorConfig(3,7,schedule='micro',mode=ModeConfig(join='sparse'),
                       leaf=LeafConfig(strategy='eliminate'))
    b=ContractorConfig(3,7,leaf=LeafConfig(strategy='eliminate'),
                       mode=ModeConfig(join='sparse'),schedule='micro')
    assert a==b


@pytest.mark.parametrize('case', PARITY_CASES, ids=lambda case:case.id)
def test_parity_unsatisfiable_reference(case):
    assert independent_count(case.kind,case.parameter,True)[0] == 0


def test_resource_configurations_reject_invalid_limits_at_construction():
    from non_exponential_sudoku.runtime.config import (
        ModeConfig, PacketConfig, LeafConfig, RecoveryConfig,
    )
    invalid = (
        lambda: ModeConfig(strategy='unsupported'),
        lambda: ModeConfig(factorization='unsupported'),
        lambda: ModeConfig(order='unsupported'),
        lambda: ModeConfig(join='unsupported'),
        lambda: ModeConfig(native_sparse='yes'),
        lambda: ModeConfig(max_modes=-7),
        lambda: ModeConfig(max_tuples=-8),
        lambda: PacketConfig(node_limit=-3),
        lambda: PacketConfig(miss_limit=-2),
        lambda: PacketConfig(cache_limit=-1),
        lambda: PacketConfig(checkpoint_coordinates=-1),
        lambda: PacketConfig(checkpoint_coordinates=1),
        lambda: LeafConfig(strategy='unsupported'),
        lambda: LeafConfig(limit=-1),
        lambda: LeafConfig(micro_threshold=-1),
        lambda: LeafConfig(adaptive_limit=-1),
        lambda: RecoveryConfig(method='unsupported'),
        lambda: RecoveryConfig(streaming=True),
        lambda: RecoveryConfig(max_jet_coordinates=0),
    )
    for factory in invalid:
        with pytest.raises(ValueError):
            factory()
    assert PacketConfig(cache_limit=0).cache_limit == 0
    assert LeafConfig(micro_threshold=0).micro_threshold == 0
