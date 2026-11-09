"""Independent edge-pair oracle and finite witnesses for the packing proof."""
from __future__ import annotations

from random import Random

import pytest

from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.packing import balanced_labels, pack
from reference.packing_proof import conditional_objective_numerator, packing_proof_record

pytestmark = pytest.mark.checkpoint


def graph(left_n: int, right_n: int, pairs: list[tuple[int, int]]) -> Network:
    left = [[] for _ in range(left_n)]
    right = [[] for _ in range(right_n)]
    for e, (i, j) in enumerate(pairs):
        left[i].append(e)
        right[j].append(e)
    def identity(*_args: object) -> int:
        return 1
    return Network(
        [Vertex(str(i), tuple(edges), identity) for i, edges in enumerate(left)],
        [Vertex(str(i), tuple(edges), identity) for i, edges in enumerate(right)],
        len(pairs),
    )


def encoded_labels(labels: tuple[tuple[int, ...], ...], r: int) -> tuple[int, ...]:
    return tuple(sum(d * (r ** i) for i, d in enumerate(label)) for label in labels)


@pytest.mark.parametrize("r,a", ((1, 2), (2, 1), (3, 1), (2, 2)))
@pytest.mark.parametrize("tie_break", ("numeric", "spread"))
def test_each_actual_greedy_choice_minimizes_exact_conditional_expectation(
    r: int, a: int, tie_break: str,
) -> None:
    rng = Random(1729)
    samples = [
        graph(4, 4, []),
        graph(4, 4, [(0, 0)] * 4 + [(1, 0), (1, 1), (2, 2), (3, 3)]),
        graph(4, 4, [(0, 0), (1, 1), (2, 2), (3, 3)]),
        graph(6, 5, [(0, 0), (1, 1), (2, 2), (3, 3), (4, 0), (5, 0)]),
    ]
    samples += [graph(4, 4, [(rng.randrange(4), rng.randrange(4)) for _ in range(9)])
                for _ in range(4)]
    R = r ** a
    for net in samples:
        lvec, rvec = balanced_labels(net, r, a, tie_break=tie_break)  # type: ignore[arg-type]
        left = encoded_labels(lvec, r)
        right = encoded_labels(rvec, r)
        partial_left: tuple[int, ...] = ()
        partial_right: tuple[int, ...] = ()
        previous = conditional_objective_numerator(net, R, (), ())
        for index, choice in enumerate(left):
            outcomes = [conditional_objective_numerator(net, R, partial_left + (k,), ())
                        for k in range(R)]
            assert outcomes[choice] == min(outcomes), (r, a, tie_break, "left", index)
            assert outcomes[choice] <= previous
            previous = outcomes[choice]
            partial_left += (choice,)
        for index, choice in enumerate(right):
            outcomes = [conditional_objective_numerator(net, R, left, partial_right + (k,))
                        for k in range(R)]
            assert outcomes[choice] == min(outcomes), (r, a, tie_break, "right", index)
            assert outcomes[choice] <= previous
            previous = outcomes[choice]
            partial_right += (choice,)
        actual = packing_proof_record(net, pack(net, r, a, (lvec, rvec)))
        assert (conditional_objective_numerator(net, R, (), ())
                == actual.initial_objective_numerator)
        assert previous == actual.final_objective_numerator
        assert actual.final_objective_numerator <= actual.initial_objective_numerator


@pytest.mark.parametrize("r,a,n,degree,parallel", (
    (2, 1, 64, 4, False), (3, 1, 192, 6, False),
    (2, 2, 512, 16, True),
))
def test_complete_numerical_packing_hypotheses_in_nontrivial_network(
    r: int, a: int, n: int, degree: int, parallel: bool,
) -> None:
    # Degree-regular bipartite circulant: M=n*degree, Delta=degree.
    net = graph(n, n, [(v, (v + (j // 2 if parallel else j)) % n)
                       for v in range(n) for j in range(degree)])
    record = packing_proof_record(net, pack(net, r, a))
    assert record.numerical_hypotheses_met
    assert record.greedy_objective_bound_met
    assert record.padding_bound_met
    assert record.packet_bound_met
    assert record.coordinate_bound_met
    assert record.packet_count <= record.padded_full_alphabet_packet_count


def test_counterfactual_sudoku_packing_is_not_declared_a_theorem_failure() -> None:
    from non_exponential_sudoku.sudoku.three_cnf import Puzzle
    from non_exponential_sudoku.sudoku.encoding import sudoku_network
    net = sudoku_network(Puzzle(2, (0,) * 16))
    record = packing_proof_record(net, pack(net, 64, 2))
    assert not record.numerical_hypotheses_met
    assert record.final_objective_numerator <= record.initial_objective_numerator
    assert not record.packet_bound_met
