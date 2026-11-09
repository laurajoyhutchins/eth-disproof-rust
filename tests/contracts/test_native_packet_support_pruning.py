"""Target-conditioned exact packet DP must not materialize dead states."""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import random

import pytest

from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.runtime.cost_ledger import CostLedger

pytestmark = [pytest.mark.checkpoint, pytest.mark.requires_native]


def _reference(bits, ring, left_positions, row_cauchy, contributions, desired):
    """Independent tuple-exponent reference, deliberately without pruning."""
    zero = ring.zero
    coefficients = {(0,) * len(desired): ring.one}
    for x, (idx, row) in enumerate(zip(left_positions, row_cauchy)):
        local = zero
        for position, weight in row:
            if bits[position]:
                local = ring.add(local, weight)
        constant = local if bits[idx] else ring.sub(ring.one, local)
        active = tuple(
            (k, weight if bits[idx] else ring.neg(weight))
            for k, weight in contributions[x]
        )
        next_coefficients = defaultdict(lambda: zero)
        for powers, value in coefficients.items():
            next_coefficients[powers] = ring.add(
                next_coefficients[powers], ring.mul(value, constant),
            )
            for index, weight in active:
                if powers[index] < desired[index]:
                    new_powers = list(powers)
                    new_powers[index] += 1
                    exponent = tuple(new_powers)
                    next_coefficients[exponent] = ring.add(
                        next_coefficients[exponent], ring.mul(value, weight),
                    )
        coefficients = next_coefficients
    return coefficients.get(desired, zero)


@pytest.mark.parametrize("jet_degree", (0, 3))
@pytest.mark.parametrize("mode_count", (1, 2, 3))
def test_native_packet_suffix_pruning_matches_unpruned_reference(
    jet_degree: int, mode_count: int,
) -> None:
    native = pytest.importorskip("native_recursive")
    base = Padic(3, modulus_polynomial(3), 17)
    ring = JetRing(base, jet_degree) if jet_degree else base
    rng = random.Random(271828 + jet_degree * 271 + mode_count * 27)
    for _ in range(48):
        count = rng.randrange(1, 7)
        desired = tuple(rng.randrange(0, 4) for _ in range(mode_count))
        left_positions = tuple(2 * i for i in range(count))
        row_cauchy = tuple(
            tuple((2 * i + 1, ring.scalar(rng.choice((0, 1, 2, 3))))
                  for _ in range(rng.randrange(0, 3)))
            for i in range(count)
        )
        contributions = tuple(
            tuple((rng.randrange(mode_count), ring.scalar(rng.choice((0, 0, 1, 2, 3))))
                  for _ in range(rng.randrange(0, mode_count + 2)))
            for i in range(count)
        )
        bits = tuple(rng.randrange(2) for _ in range(2 * count))
        expected = _reference(
            bits, ring, left_positions, row_cauchy, contributions, desired,
        )
        got = native.packet_evaluate(
            bits, ring, left_positions, row_cauchy, contributions, desired,
            (), tuple((2 * i + 1, 2 * i + 1) for i in range(count)),
            positions_are_bits=True,
        )
        assert got == expected


def test_impossible_target_does_not_enter_coefficient_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 19)
    contribution = ring.scalar(3)
    cauchy = ring.scalar(2)
    def forbidden(*_args):
        raise AssertionError("an unreachable coefficient must not be multiplied")
    with monkeypatch.context() as patch:
        patch.setattr(Padic, "mul", forbidden)
        got = native.packet_evaluate(
            (1, 1), ring, (0,), (((1, cauchy),),),
            (((0, contribution),),), (2,), (), ((1, 1),),
            positions_are_bits=True,
        )
    assert got == ring.zero


def test_suffix_pruning_reduces_observed_multiplication_calls() -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 19)
    # The first half can only contribute to mode 0; the second half
    # can only contribute to mode 1. Each row contributes at most once.
    rows = 8
    bits = (1, 1) * rows
    positions = tuple(2 * i for i in range(rows))
    cauchy = tuple(((2 * i + 1, ring.scalar(2)),) for i in range(rows))
    contributions = tuple(
        ((0 if i < rows // 2 else 1, ring.scalar(3)),)
        for i in range(rows)
    )
    desired = (4, 4)
    ledger_ref = CostLedger()
    with ledger_ref.frame(depth=0, wires=1, precision=19,
                          ring_depth=0, schedule="micro"):
        reference = _reference(
            bits, ring, positions, cauchy, contributions, desired,
        )
    ledger_native = CostLedger()
    with ledger_native.frame(depth=0, wires=1, precision=19,
                             ring_depth=0, schedule="micro"):
        answer = native.packet_evaluate(
            bits, ring, positions, cauchy, contributions, desired,
            (), tuple((2 * i + 1, 2 * i + 1) for i in range(rows)),
            positions_are_bits=True,
        )
    assert answer == reference
    def mul_calls(ledger):
        return sum(v for key, v in ledger.total_ring_calls.items()
                   if key[2] == "mul")
    assert mul_calls(ledger_native) < mul_calls(ledger_ref)
    assert ledger_native.report()["frame_tree_reconciled"]


def test_large_target_keeps_sparse_key_arithmetic_bounded() -> None:
    native = pytest.importorskip("native_recursive")
    ring = Padic(3, modulus_polynomial(3), 9)
    bits = (1, 1)
    row = (((1, ring.scalar(3)),),)
    contributions = (((0, ring.scalar(7)),),)
    # Cap is >512 so the original sparse DP would be selected, but
    # the desired exponent cannot be reached by one linear factor.
    assert native.packet_evaluate(
        bits, ring, (0,), row, contributions, (513,), (), ((1, 1),),
        positions_are_bits=True,
    ) == ring.zero
