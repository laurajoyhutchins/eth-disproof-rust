"""Adversarial contracts for shift-left equivalence, retention, and refusals."""
from __future__ import annotations

from dataclasses import replace
from itertools import product
from random import Random

import pytest

from benchmarks.recursive_cases import get_case
from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, LeafConfig, Padic
from non_exponential_sudoku.core.algebra import modulus_polynomial
from non_exponential_sudoku.core.modes import mode_catalog
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.state import SupportProjectionLimits, support_projected_domains
from non_exponential_sudoku.sudoku.frontier import count_frontier
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.runtime.budget import CapacityError
from reference.local_support import projected_domains
from reference.generalized_bench import canonical_solution

pytestmark = pytest.mark.checkpoint


def test_exhaustive_four_by_four_tensor_entries() -> None:
    for clue in (0, 1, 4):
        puzzle = Puzzle(2, (clue,) + (0,) * 15)
        old = DirectNetwork.from_puzzle(puzzle)
        new = sudoku_network(puzzle)
        ring = Padic(5, modulus_polynomial(5), 5)
        for v1, v2 in zip(old.vertices, new.left + new.right):
            for bits in product((0, 1), repeat=len(v1.ports)):
                edge_assignment = [0] * old.edge_count
                for e, bit in zip(v1.ports, bits):
                    edge_assignment[e] = bit
                assert v2.oracle(bits, ring) == ring.scalar(old.local_entry(v1, edge_assignment))
            for invalid in ((0,) * (len(v1.ports) - 1), (0,) * len(v1.ports) + (0,),
                            (2,) + (0,) * (len(v1.ports) - 1)):
                with pytest.raises(ValueError, match='port|Boolean'):
                    v2.oracle(invalid, ring)


def test_compiled_oracle_accepts_reference_boolean_equivalents() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    reference = DirectNetwork.from_puzzle(puzzle)
    compiled = sudoku_network(puzzle)
    ring = Padic(5, modulus_polynomial(5), 5)
    for source, target in zip(reference.vertices, compiled.left + compiled.right):
        for bit in (0.0, 1.0):
            bits = (bit,) * len(source.ports)
            assignment = [0] * reference.edge_count
            for edge, value in zip(source.ports, bits):
                assignment[edge] = value
            assert target.oracle(bits, ring) == ring.scalar(
                reference.local_entry(source, assignment))


def test_random_matching_projection_matches_independent_fixed_point() -> None:
    rng = Random(12870)
    for block, clues, repetitions in ((2, (0, 2, 4, 8, 12, 15), 10),
                                        (3, (71, 77, 80), 5)):
        solution = canonical_solution(block)
        for amount in clues:
            for _ in range(repetitions):
                chosen = set(rng.sample(range(len(solution)), amount))
                puzzle = Puzzle(block, tuple(value if cell in chosen else 0
                                             for cell, value in enumerate(solution)))
                actual = support_projected_domains(puzzle)
                reference, _ = projected_domains(puzzle, method='matching')
                assert actual == reference
                if block == 2:
                    assert count_frontier(puzzle).count == count_frontier(
                        puzzle, projection='matching').count


@pytest.mark.parametrize('puzzle', (
    Puzzle(0, ()),
    Puzzle(2, (0,) * 15),
    Puzzle(2, (99,) + (0,) * 15),
))
def test_matching_projection_rejects_invalid_puzzles(puzzle: Puzzle) -> None:
    with pytest.raises(ValueError, match='Invalid Sudoku'):
        support_projected_domains(puzzle)


def test_matching_projection_candidate_budget_precedes_allocation() -> None:
    with pytest.raises(CapacityError, match='candidate limit'):
        support_projected_domains(Puzzle(2, (0,) * 16),
                                  limits=SupportProjectionLimits(max_candidates=63))


def _crossing(size: int):
    from non_exponential_sudoku.core.network import simple_network
    net = simple_network(size,
        [([j], {(0,): 1, (1,): 1}) for j in range(size)],
        [([j], {(0,): 1, (1,): 1}) for j in range(size)])
    packing = pack(net, 64, 2,
        (tuple((0, 0) for _ in range(size)),
         tuple((1, 0) for _ in range(size))))
    return net, packing


def test_reused_public_plan_cache_cannot_alias_different_network() -> None:
    from non_exponential_sudoku.contraction.valuation_cache import ValuationCache
    from non_exponential_sudoku.runtime.cache import CachePolicy
    config = ContractorConfig(4, 9, schedule='geometry64',
                              mode=ModeConfig(factorization='components'),
                              leaf=LeafConfig(strategy='eliminate'))
    engine = ContractionEngine(config)
    ring = Padic(engine.e, engine.f, 9)
    cache = ValuationCache(CachePolicy(max_bytes=8 * 1024 * 1024))
    for size in (2, 4):
        net, packing = _crossing(size)
        modes = mode_catalog(net, packing, 1, ring.p)
        expected = engine.evaluate_deformation(net, packing, modes, 1,
                                               ring.basis(3), ring, 0)
        actual = engine.evaluate_deformation(net, packing, modes, 1,
                                             ring.basis(3), ring, 0,
                                             factor_plan_cache=cache)
        assert actual == expected == ring.scalar(1 << size)
    cache.clear()


def test_valuation_structure_cache_respects_shared_budget() -> None:
    from non_exponential_sudoku.contraction.valuation_cache import ValuationCache
    from non_exponential_sudoku.runtime.cache import CachePolicy, SharedCacheBudget
    net, packing = _crossing(2)
    ring = Padic(5, modulus_polynomial(5), 9)
    modes = mode_catalog(net, packing, 1, ring.p)
    shared = SharedCacheBudget(128)
    cache = ValuationCache(CachePolicy(max_bytes=8*1024*1024), shared=shared)
    assert not cache.store_modes(net, packing, modes, 0, ring.p)
    assert cache.get_modes(net, packing, 0, ring.p) is None
    assert shared.peak_bytes <= shared.max_bytes
    cache.clear()
    assert shared.live_bytes == 0


def test_valuation_cache_reservations_release_on_error(monkeypatch) -> None:
    case = get_case('parity-2wire', 'plans')
    cfg = replace(case.config, recursion=replace(case.config.recursion,
                  shared_cache_bytes=1_000_000))
    engine = ContractionEngine(cfg)

    def failure(*args, **kwargs):
        raise CapacityError('Injected evaluation failure')

    monkeypatch.setattr(engine, '_jet_center', failure)
    with pytest.raises(CapacityError, match='Injected evaluation failure'):
        engine.contract(case.network)
    assert engine.shared_cache is not None
    assert engine.shared_cache.peak_bytes > 0
    assert engine.shared_cache.live_bytes == 0


def test_tight_budget_preserves_recursion_counts() -> None:
    case = get_case('nested-2wire', 'plans')
    from non_exponential_sudoku.runtime.cache import CachePolicy
    baseline = ContractionEngine(case.config).contract(case.network)
    cfg = replace(case.config, recursion=replace(case.config.recursion,
                    shared_cache_bytes=1024,
                    valuation_structures=CachePolicy(max_bytes=8*1024*1024)))
    engine = ContractionEngine(cfg)
    assert engine.contract(case.network) == baseline
    assert engine.shared_cache is not None
    assert engine.shared_cache.live_bytes == 0
    assert engine.stats.shared_cache_peak_estimated_bytes <= 1024
