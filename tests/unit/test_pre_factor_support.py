"""TDD: a local zero proof must precede child-factor evaluation and budget charge."""
from __future__ import annotations

from dataclasses import replace
from itertools import product

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import ContractionEngine, ZeroSupportPolicy
from non_exponential_sudoku.contraction.compiled_children import CompiledChildPlan
from non_exponential_sudoku.contraction.packets import EvaluationContext
from non_exponential_sudoku.contraction.pre_factor_support import certify_pre_factor_zero
from non_exponential_sudoku.contraction.zero_support import certify_zero
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.core.network import simple_network
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.runtime.config import ModeLimits
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.elimination.engine import ModeEliminator


def run_case(name: str, *, pre_factor: bool):
    case = get_case(name, 'plans')
    cfg = replace(case.config, recursion=replace(
        case.config.recursion,
        zero_support=ZeroSupportPolicy(enabled=True, pre_factor=pre_factor)))
    engine = ContractionEngine(cfg)
    result = engine.contract(case.network)[0]
    assert result == case.expected
    return engine.stats


@pytest.mark.parametrize('name', (
    pytest.param('sudoku-4wire', marks=pytest.mark.checkpoint),
    pytest.param('nested-2wire', marks=pytest.mark.integration),
))
def test_prefactor_reduces_charged_children_without_changing_count(name: str) -> None:
    before = run_case(name, pre_factor=False)
    after = run_case(name, pre_factor=True)
    assert after.pre_factor_attempts > 0
    assert after.pre_factor_certificates > 0
    assert after.mode_dp_local_child_evaluations < before.mode_dp_local_child_evaluations
    assert after.pre_factor_certificates == (
        before.mode_dp_local_child_evaluations - after.mode_dp_local_child_evaluations)
    assert after.pre_factor_attempts == before.mode_dp_local_child_evaluations


@pytest.mark.integration
def test_prefactor_eight_wire_exact_count_and_cost() -> None:
    before = run_case('sudoku-8wire', pre_factor=False)
    after = run_case('sudoku-8wire', pre_factor=True)
    assert after.pre_factor_certificates >= 1
    assert after.mode_dp_local_child_evaluations < before.mode_dp_local_child_evaluations
    assert before.mode_dp_local_child_evaluations == after.pre_factor_attempts


@pytest.mark.checkpoint
def test_certificate_has_no_false_zeros_against_actual_children() -> None:
    for n in (1, 2, 3):
        net = simple_network(n,
            [((j,), {(0,): 1, (1,): 1}) for j in range(n)],
            [((j,), {(0,): 1, (1,): 1}) for j in range(n)])
        packing = pack(net, 64, 2,
            (tuple((0, 0) for _ in range(n)),
             tuple((1, 0) for _ in range(n))))
        ring = Padic(5, modulus_polynomial(5), 5)
        modes = mode_catalog(net, packing, 1, ring.p)
        context = EvaluationContext(1, ring.basis(1), ring, packing.a)
        plan = CompiledChildPlan(net, packing, 0, 0)
        policy = ZeroSupportPolicy(enabled=True, pre_factor=True)
        checked = 0
        for beta in product(*(range(min(1, len(m.rows)) + 1) for m in modes)):
            # The fixture is small; compare each eligible beta exhaustively.
            result = certify_pre_factor_zero(plan, modes, beta, ring, policy)
            child = plan.instantiate(modes, beta, 1, ring.basis(1), ring, context)
            post = certify_zero(child, ring, policy)
            if result.verdict == 'zero':
                assert post.verdict == 'zero'
                assert child.direct(ring, child.edges) == ring.zero
            checked += 1
        assert checked > 0


@pytest.mark.checkpoint
def test_pre_factor_refusal_falls_back_to_exact_child() -> None:
    case = get_case('sudoku-4wire', 'plans')
    cfg = replace(case.config, recursion=replace(
        case.config.recursion,
        zero_support=ZeroSupportPolicy(enabled=True, pre_factor=True,
                                       max_child_edges=1)))
    engine = ContractionEngine(cfg)
    assert engine.contract(case.network)[0] == case.expected
    assert engine.stats.pre_factor_unsupported == engine.stats.pre_factor_attempts
    assert engine.stats.pre_factor_certificates == 0


@pytest.mark.integration
def test_child_limit_applies_to_uncertified_work_not_upper_bound() -> None:
    case = get_case('sudoku-4wire', 'plans')
    baseline = run_case('sudoku-4wire', pre_factor=True)
    assert baseline.mode_dp_local_child_evaluations > 0
    cfg = replace(case.config,
        limits=replace(case.config.limits,
                       max_child_contractions=baseline.mode_dp_local_child_evaluations),
        recursion=replace(case.config.recursion,
            zero_support=ZeroSupportPolicy(enabled=True, pre_factor=True)))
    engine = ContractionEngine(cfg)
    assert engine.contract(case.network)[0] == case.expected


@pytest.mark.checkpoint
def test_policy_is_explicit_and_typed() -> None:
    assert not ZeroSupportPolicy().pre_factor
    with pytest.raises(ValueError):
        ZeroSupportPolicy(pre_factor=1)
    with pytest.raises(ValueError):
        ZeroSupportPolicy(pre_factor=True, enabled=False)

@pytest.mark.checkpoint
def test_standalone_factor_builder_skips_certified_rows_before_budget_charge() -> None:
    from non_exponential_sudoku.core.modes import Mode
    modes = [Mode(j, 0, 0, 0, 1, 1, (), (0,)) for j in range(8)]
    ring = Padic(5, modulus_polynomial(5), 9)
    counts = {'child': 0, 'certificate': 0}

    def preflight(group, scope, assignment):
        if any(assignment):
            counts['certificate'] += 1
            return True
        return False

    def child(group, scope, assignment):
        counts['child'] += 1
        assert not any(assignment)
        return ring.one

    stats = Counters()
    runner = ModeEliminator(
        modes, {0,1}, ring, child, stats, CapacityError,
        limits=ModeLimits(max_factor_states=500, max_child_contractions=2),
        native_sparse=False, prove_zero=preflight)
    assert runner.run() == ring.one
    assert counts == {'child':2, 'certificate':510}
    assert stats.mode_dp_local_child_evaluations == 2


@pytest.mark.integration
def test_pre_factor_cache_budget_does_not_change_exact_result() -> None:
    from non_exponential_sudoku.runtime.cache import CachePolicy
    case = get_case('sudoku-4wire', 'plans')
    for budget in (1, 1024, 8192):
        cfg = replace(case.config, recursion=replace(
            case.config.recursion,
            pre_factor_support_cache=CachePolicy(max_bytes=budget, max_entries=2),
            shared_cache_bytes=16384,
            zero_support=ZeroSupportPolicy(enabled=True, pre_factor=True)))
        engine = ContractionEngine(cfg)
        assert engine.contract(case.network)[0] == case.expected
        assert engine.shared_cache is not None
        assert engine.shared_cache.live_bytes == 0
        assert engine.shared_cache.peak_bytes <= 16384
        assert engine.stats.pre_factor_certificates == 4


@pytest.mark.integration
def test_pre_factor_clears_cached_support_on_child_refusal() -> None:
    from non_exponential_sudoku.runtime.cache import CachePolicy
    case = get_case('sudoku-4wire', 'plans')
    cfg = replace(case.config,
        limits=replace(case.config.limits, max_child_contractions=1),
        recursion=replace(case.config.recursion,
            shared_cache_bytes=100000,
            zero_support=ZeroSupportPolicy(enabled=True, pre_factor=True)))
    engine = ContractionEngine(cfg)
    with pytest.raises(CapacityError):
        engine.contract(case.network)
    assert engine.shared_cache is not None
    assert engine.shared_cache.live_bytes == 0
    assert engine.stats.pre_factor_attempts > 0


@pytest.mark.checkpoint
def test_explicit_mode_budget_is_a_fallback_not_a_zero() -> None:
    case = get_case('sudoku-4wire', 'plans')
    cfg = replace(case.config, recursion=replace(
        case.config.recursion,
        zero_support=ZeroSupportPolicy(enabled=True, pre_factor=True,
                                       max_mode_terms=1)))
    engine = ContractionEngine(cfg)
    assert engine.contract(case.network)[0] == case.expected
    # Every supported assignment still returns its exact result.
    assert engine.stats.pre_factor_attempts > 0
    with pytest.raises(ValueError):
        ZeroSupportPolicy(max_mode_terms=0)
