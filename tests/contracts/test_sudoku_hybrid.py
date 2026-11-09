"""Exact hybrid Sudoku representation migration and resource contracts."""
from __future__ import annotations

from math import comb, factorial, prod
from random import Random

import pytest

from non_exponential_sudoku.sudoku.frontier import FrontierCapacityError, FrontierLimits, count_frontier
from non_exponential_sudoku.sudoku.hybrid import (
    HybridLimits, _Conversions, _pack, _unpack, contract_hybrid,
)
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.sudoku.weighted_zdd import _Budget, ZDDLimits, contract_zdd
from reference.generalized_bench import canonical_solution
from reference.mrv_count import count_mrv_reference
from reference.real_sudoku_bench import puzzles

pytestmark = pytest.mark.checkpoint


def test_exact_round_trip_preserves_weighted_signatures() -> None:
    rng = Random(380038)
    for _ in range(75):
        table = {rng.randrange(1 << 13): rng.randrange(1, 1 << 30)
                 for _ in range(rng.randrange(1, 38))}
        source = dict(sorted(table.items()))
        diagram, root = _pack(source, _Budget(ZDDLimits()), _Conversions(1_000_000))
        assert diagram.totals(root)[:2] == (sum(source.values()), len(source))
        assert _unpack(diagram, root, len(source), _Conversions(1_000_000)) == source
    assert _unpack(*_pack({}, _Budget(ZDDLimits()), _Conversions(100)),
                   1, _Conversions(100)) == {}


def test_switching_on_permutation_rich_prefixes() -> None:
    # The normal frontier refuses before these large prefix counts finish.
    empty = Puzzle(3, (0,) * 81)
    result = contract_hybrid(empty, prefix_cells=9)
    assert result.count == factorial(9)
    assert result.stats.dictionary_to_diagram == 1
    assert len(result.stats.layers) == 9
    assert [layer.step for layer in result.stats.layers] == list(range(1, 10))
    assert sum(layer.switch == 'to-zdd' for layer in result.stats.layers) == 1
    assert result.stats.layers[-1].represented_states == factorial(9)
    assert result.stats.layers[-1].live_diagram_nodes == 3648
    assert result.stats.peak_dictionary_states < 10_000
    assert result.stats.final_nodes == 3648
    assert result.stats.final_representation == 'zdd'
    assert not result.stats.complete
    sixteen = Puzzle(4, (0,) * 256)
    larger = contract_hybrid(sixteen, prefix_cells=5)
    assert larger.count == prod(range(12, 17))
    assert larger.stats.dictionary_to_diagram == 1
    assert larger.stats.peak_dictionary_states < 10_000
    assert larger.stats.final_nodes < 2000
    with pytest.raises(FrontierCapacityError, match='state limit'):
        count_frontier(sixteen, limits=FrontierLimits(max_states=100_000))


def test_fully_pinned_digit_labels_still_allow_hybrid_compression() -> None:
    solved = canonical_solution(3)
    pinned = Puzzle(3, tuple(digit if index // 9 == 8 else 0
                             for index, digit in enumerate(solved)))
    expected = sum((-1)**k * comb(9, k) * factorial(9-k) for k in range(10))
    result = contract_hybrid(pinned, prefix_cells=9)
    assert expected == result.count == 133496
    assert result.stats.dictionary_to_diagram == 1
    assert result.stats.final_representation == 'zdd'


def test_hard_puzzle_avoids_unhelpful_conversion() -> None:
    hard = next(p for name, p, _ in puzzles() if name == '9x9-hard-unique')
    for order in ('row-major', 'reachable'):
        result = contract_hybrid(hard, order=order)
        assert result.count == count_frontier(hard).count == 1
        assert result.stats.dictionary_to_diagram == 0
        assert result.stats.diagram_to_dictionary == 0
        assert result.stats.conversion_work == 0
    assert contract_hybrid(hard, order='reachable').stats.peak_dictionary_states == 268


def test_reachable_sixteen_declines_unprofitable_conversion() -> None:
    solution = canonical_solution(4)
    retained = set(Random(1).sample(range(256), 120))
    puzzle = Puzzle(4, tuple(digit if cell in retained else 0
                             for cell, digit in enumerate(solution)))
    result = contract_hybrid(puzzle, order='reachable')
    assert result.count == 177
    assert result.stats.sample_rejections >= 1
    assert result.stats.dictionary_to_diagram == 0
    assert result.stats.peak_dictionary_states == 3592


def test_randomized_full_and_restricted_sudoku_agrees_with_independent_counter() -> None:
    rng = Random(380103)
    solved = canonical_solution(2)
    for _ in range(30):
        retained = set(rng.sample(range(16), rng.randrange(16)))
        puzzle = Puzzle(2, tuple(digit if cell in retained else 0
                                 for cell, digit in enumerate(solved)))
        oracle, _ = count_mrv_reference(puzzle)
        for order in ('row-major', 'minimum-domain', 'reachable'):
            assert contract_hybrid(puzzle, order=order).count == oracle
        domains = tuple((1 << (digit - 1)) if cell in retained else
                        15 ^ (1 << rng.randrange(4))
                        for cell, digit in enumerate(solved))
        assert contract_hybrid(puzzle, domains=domains).count == count_frontier(
            puzzle, domains=domains).count
    assert contract_hybrid(Puzzle(2, (1, 1) + (0,) * 14)).count == 0
    assert contract_hybrid(Puzzle(1, (1,))).count == 1


def test_limits_refuse_without_silent_fallback() -> None:
    empty = Puzzle(2, (0,) * 16)
    with pytest.raises(FrontierCapacityError, match='dictionary state limit'):
        contract_hybrid(empty, limits=HybridLimits(frontier=FrontierLimits(max_states=1)))
    with pytest.raises(FrontierCapacityError, match='dictionary transition limit'):
        contract_hybrid(empty, limits=HybridLimits(frontier=FrontierLimits(max_transitions=1)))
    with pytest.raises(FrontierCapacityError, match='estimated-byte limit'):
        contract_hybrid(empty, limits=HybridLimits(frontier=FrontierLimits(max_estimated_bytes=1)))
    with pytest.raises(FrontierCapacityError, match='coefficient-bit limit'):
        contract_hybrid(empty,
                        limits=HybridLimits(diagram=ZDDLimits(max_coefficient_bits=1)))
    with pytest.raises(FrontierCapacityError, match='conversion-work limit'):
        contract_hybrid(Puzzle(3, (0,) * 81), prefix_cells=9,
                        limits=HybridLimits(max_conversion_work=1))
    with pytest.raises(ValueError, match='hybrid prefix length'):
        contract_hybrid(empty, prefix_cells=17)
    with pytest.raises(ValueError, match='hybrid prefix length'):
        contract_hybrid(empty, prefix_cells=True)  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='cell order'):
        contract_hybrid(empty, order='invalid')  # type: ignore[arg-type]
    with pytest.raises(ValueError, match='bit order'):
        contract_hybrid(empty, bit_order='invalid')  # type: ignore[arg-type]
    for kw in ({'min_switch_states': 0}, {'max_conversion_states': 0},
               {'min_savings_percent': 100}, {'switch_cooldown': -1},
               {'max_switch_attempts': -1}, {'sample_probe_states': 0},
               {'max_sample_nodes_per_state': 0}, {'max_conversion_work': 0}):
        with pytest.raises(ValueError, match='Invalid hybrid limits'):
            HybridLimits(**kw)


def test_starting_from_diagram_switches_back_when_dictionary_is_smaller() -> None:
    for base in (2, 3):
        puzzle = Puzzle(base, (0,) * (base**4))
        result = contract_hybrid(puzzle, initial='zdd', prefix_cells=2)
        assert result.count == puzzle.side * (puzzle.side - 1)
        assert result.stats.diagram_to_dictionary == 1
        assert result.stats.layers[0].switch == 'to-dictionary'
        assert result.stats.layers[-1].representation == 'dictionary'
        assert result.stats.dictionary_to_diagram == 0
        assert result.stats.final_representation == 'dictionary'
    assert contract_hybrid(Puzzle(2, (0,) * 16), initial='zdd').count == 288
    with pytest.raises(ValueError, match='initial representation'):
        contract_hybrid(Puzzle(2, (0,) * 16), initial='invalid')  # type: ignore[arg-type]


def test_no_switch_keeps_exact_dictionary_semantics() -> None:
    puzzle = Puzzle(2, (0,) * 16)
    disabled = contract_hybrid(puzzle, limits=HybridLimits(max_switch_attempts=0))
    assert disabled.count == 288
    assert disabled.stats.dictionary_to_diagram == 0
    assert disabled.stats.conversion_work == 0
    assert contract_zdd(puzzle).count == disabled.count


def test_projection_preflight_retains_profitable_switches_without_trial_diagram() -> None:
    """The predictor inspects bit-block projections, never a trial ZDD."""
    for side, prefix, expected in ((3, 9, factorial(9)),
                                   (4, 5, prod(range(12, 17)))):
        puzzle = Puzzle(side, (0,) * (side**4))
        predicted = contract_hybrid(puzzle, prefix_cells=prefix,
                                    limits=HybridLimits(preflight='projected-blocks'))
        historical = contract_hybrid(
            puzzle, prefix_cells=prefix,
            limits=HybridLimits(preflight='sample-zdd'))
        assert predicted.count == historical.count == expected
        assert predicted.stats.dictionary_to_diagram == 1
        assert predicted.stats.final_representation == 'zdd'
        assert predicted.stats.final_nodes == historical.stats.final_nodes
        assert predicted.stats.prediction_checks == 1
        assert predicted.stats.prediction_rejections == 0
        assert predicted.stats.prediction_work <= (side * side) * 64
        assert predicted.stats.conversion_work < historical.stats.conversion_work
        switched = [layer for layer in predicted.stats.layers
                    if layer.switch == 'to-zdd']
        assert len(switched) == 1
        assert switched[0].sampled_max_block_variants is not None
        assert switched[0].sampled_max_block_variants <= 12


def test_projection_preflight_rejects_difficult_sixteen_without_trial_diagram() -> None:
    solution = canonical_solution(4)
    retained = set(Random(1).sample(range(256), 120))
    puzzle = Puzzle(4, tuple(digit if cell in retained else 0
                             for cell, digit in enumerate(solution)))
    predicted = contract_hybrid(puzzle, order='reachable',
                                limits=HybridLimits(preflight='projected-blocks'))
    historical = contract_hybrid(
        puzzle, order='reachable', limits=HybridLimits(preflight='sample-zdd'))
    assert predicted.count == historical.count == 177
    assert predicted.stats.peak_dictionary_states == historical.stats.peak_dictionary_states
    assert predicted.stats.dictionary_to_diagram == 0
    assert predicted.stats.conversion_work == 0
    assert historical.stats.conversion_work > 0
    assert predicted.stats.prediction_checks == predicted.stats.prediction_rejections == 2
    assert predicted.stats.sample_rejections == 2
    assert max(layer.sampled_max_block_variants or 0
               for layer in predicted.stats.layers) >= 22


def test_projection_is_only_a_refusal_heuristic_and_has_work_limit() -> None:
    empty = Puzzle(3, (0,) * 81)
    with pytest.raises(FrontierCapacityError, match='prediction-work limit'):
        contract_hybrid(empty, prefix_cells=9,
                        limits=HybridLimits(preflight='projected-blocks', max_prediction_work=1))
    # Reject every projection intentionally; exact dictionary semantics survive.
    no_attempt = contract_hybrid(empty, prefix_cells=4,
                                 limits=HybridLimits(preflight='projected-blocks', max_block_variants=1))
    assert no_attempt.count == 3024
    assert no_attempt.stats.dictionary_to_diagram == 0
    assert no_attempt.stats.prediction_rejections == 1
    # A permissive predictor cannot force a switch against measured byte cost.
    small = Puzzle(2, (0,) * 16)
    unprofitable = contract_hybrid(
        small, limits=HybridLimits(min_switch_states=4,
                                   max_conversion_states=1000,
                                   min_savings_percent=99,
                                   switch_cooldown=0,
                                   preflight='projected-blocks'))
    assert unprofitable.count == 288
    assert unprofitable.stats.dictionary_to_diagram == 0
    for limits in (HybridLimits(max_prediction_work=100_000),):
        assert limits.preflight == 'sample-zdd'
    for options in ({'max_block_variants': 0}, {'max_prediction_work': 0},
                    {'preflight': 'unknown'}):
        with pytest.raises(ValueError, match='Invalid hybrid limits'):
            HybridLimits(**options)
