"""Independent exact RREF and source-oracle tests of projected Gram bit bounds.

Source comparison is to the *pre-refactor rational algorithm*, copied
only here as a reference. Production uses integer Gram + Montante.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, lcm
from random import Random

import pytest

from non_exponential_sudoku.eth import (
    construct_bounded_designs, construct_implicit_auxiliary,
)
from non_exponential_sudoku.eth.construction import _projected_group_rows
from non_exponential_sudoku.eth.projected_gram import (
    _IntegerMeter, _fraction_free_basis, projected_gram_envelope,
    projected_group_basis, projected_transfer_gram_envelope,
)
from non_exponential_sudoku.eth.polynomial import deformation_polynomial
from non_exponential_sudoku.eth.cnf import count_bruteforce


def _old_fraction_rref(matrix: list[list[Fraction]]) -> tuple[tuple[int, ...], ...]:
    """Independent original Gaussian elimination and gcd normalization."""
    if not matrix:
        return ()
    rows = [list(row) for row in matrix]
    rank = 0
    for col in range(len(rows[0])):
        selected = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if selected is None:
            continue
        rows[rank], rows[selected] = rows[selected], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [v / scale for v in rows[rank]]
        for i, row in enumerate(rows):
            if i != rank:
                factor = row[col]
                if factor:
                    rows[i] = [a - factor * b for a, b in zip(row, rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    output: list[tuple[int, ...]] = []
    for row in rows[:rank]:
        d = 1
        for value in row:
            d = lcm(d, value.denominator)
        integers = [int(value * d) for value in row]
        g = 0
        for value in integers:
            g = gcd(g, abs(value))
        output.append(tuple(v // g for v in integers))
    return tuple(output)


def _legacy_group_rows(
    auxiliary: object, copy: dict[tuple[tuple[int, int], ...], int],
    group: tuple[int, ...],
) -> tuple[tuple[int, ...], ...]:
    from non_exponential_sudoku.eth.construction import ImplicitAuxiliaryDesign

    assert isinstance(auxiliary, ImplicitAuxiliaryDesign)
    positions = {v: i for i, v in enumerate(group)}
    mapping: dict[int, list[tuple[tuple[int, int], ...]]] = {}
    for label, v in copy.items():
        if v in positions:
            mapping.setdefault(v, []).append(label)
    active = tuple(v for v in group if v in mapping)
    if not active:
        return ()
    data: list[list[Fraction]] = []
    for variable in active:
        row = [Fraction(0) for _ in group]
        for target in active:
            row[positions[target]] = sum((
                auxiliary.exceptional_projector_at(left, right)
                for left in mapping[variable] for right in mapping[target]
            ), Fraction(0))
        data.append(row)
    return _old_fraction_rref(data)


@pytest.mark.integration
def test_integer_fraction_free_reduction_equals_independent_fraction_rref() -> None:
    rng = Random(94027)
    checked = 0
    for k in range(1, 7):
        for _ in range(70):
            rows = [[rng.randrange(-7, 8) for _ in range(k)] for _ in range(k)]
            bound = k * (
                max(1, max(abs(value).bit_length() for row in rows for value in row))
                + (k + 1).bit_length()
            ) + 6
            meter = _IntegerMeter(2 * bound + 5)
            actual = _fraction_free_basis(rows, meter, bound)
            expected = _old_fraction_rref([[Fraction(v) for v in row] for row in rows])
            assert actual == expected
            assert meter.max_bits <= 2 * bound + 5
            assert meter.bit_steps >= 0
            checked += 1
    assert checked == 420


@pytest.mark.integration
@pytest.mark.parametrize("r,Q,R", [(2, 2, 2), (2, 3, 2), (3, 2, 2)])
def test_source_projector_exact_basis_matches_previous_fraction_algorithm(
    r: int, Q: int, R: int,
) -> None:
    auxiliary = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector",
    )
    rng = Random(1039 + r * 100 + Q * 10 + R)
    group = tuple(range(5))
    for case in range(16):
        copied: dict[tuple[tuple[int, int], ...], int] = {}
        for _ in range(case + 1):
            label = tuple((rng.randrange(r), rng.randrange(r))
                          for _ in range(Q))
            copied[label] = rng.randrange(7)
        actual = projected_group_basis(auxiliary, copied, group)
        old = _legacy_group_rows(auxiliary, copied, group)
        assert actual.rows == old
        assert _projected_group_rows(auxiliary, copied, group) == old
        env = actual.stats.envelope
        assert actual.stats.exact_rank == len(old)
        assert actual.stats.queried_projector_pairs <= env.projector_query_count_upper
        assert actual.stats.max_observed_integer_bits <= env.transient_integer_bits_upper
        assert actual.stats.integer_bit_steps <= env.integer_work_bit_steps_upper
        assert all(
            max((abs(x).bit_length() for x in row), default=0)
            <= env.primitive_basis_bits_upper
            for row in actual.rows
        )


@pytest.mark.integration
def test_real_projected_transfer_keeps_center_measurement_certificates_and_count() -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula
    from non_exponential_sudoku.eth import taylor_coefficients_separated

    formula = ring_formula(6, width=2)
    built = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    expected = count_bruteforce(formula)
    assert deformation_polynomial(formula, built.replacements).at_zero == expected
    for center, design in built.centers:
        actual = taylor_coefficients_separated(
            formula, design, built.replacements,
            at=center, order=0, summation="eliminate",
        )
        assert actual.coefficients


@pytest.mark.integration
def test_huge_virtual_auxiliary_projected_group_is_live_and_bounded() -> None:
    r, Q, R = 17, 12, 3
    auxiliary = construct_implicit_auxiliary(
        r=r, Q=Q, R=R, measurement_basis="projector",
    )
    labels = [
        tuple((v + s) % r for _ in range(2)) for v in range(1)
        for s in range(0)
    ]
    assert labels == []
    labels_by_var = {
        tuple(((i + 2 * s) % r, (i + 2 * s + 1) % r)
              for s in range(Q)): i
        for i in range(4)
    }
    result = projected_group_basis(auxiliary, labels_by_var, (0, 1, 2, 3, 4))
    assert auxiliary.dimension == 17 ** 24
    assert result.stats.envelope.occupied_labels == 4
    assert result.stats.queried_projector_pairs <= 16
    assert result.stats.peak_matrix_entries <= 16
    assert result.stats.integer_bit_steps < result.stats.envelope.integer_work_bit_steps_upper
    assert _projected_group_rows(auxiliary, labels_by_var, (0, 1, 2, 3, 4)) == result.rows


@pytest.mark.checkpoint
def test_zero_rank_empty_group_and_symbolic_bounds_do_not_allocate_D() -> None:
    auxiliary = construct_implicit_auxiliary(
        r=2, Q=2, R=2, measurement_basis="projector",
    )
    label = ((0, 0), (0, 1))
    empty = projected_group_basis(auxiliary, {label: 77}, (0, 1))
    assert empty.rows == ()
    assert empty.stats.exact_rank == 0
    for k in (0, 1, 3):
        bound = projected_gram_envelope(
            group_size=5, occupied_labels=max(k, 1),
            active_variables=k, r=2, Q=3, R=2,
        )
        assert bound.primitive_basis_bits_upper > 0
    huge = projected_gram_envelope(
        group_size=10 ** 30, occupied_labels=10 ** 15,
        active_variables=10 ** 12, r=10**5, Q=10 ** 5, R=10 ** 4,
    )
    assert huge.integer_work_bit_steps_upper > 0
    assert huge.retained_abstract_bit_cells_upper > 0
    assert huge.stored_minor_bits_upper > huge.gram_entry_bits_upper
    assert huge.projector_query_count_upper == 10 ** 30


@pytest.mark.checkpoint
def test_bad_dimensions_refuse_without_a_fictitious_certificate() -> None:
    with pytest.raises(ValueError, match="invalid"):
        projected_gram_envelope(
            group_size=2, occupied_labels=1, active_variables=2,
            r=2, Q=2, R=2,
        )
    with pytest.raises(ValueError, match="duplicate"):
        a = construct_implicit_auxiliary(r=2, Q=2, R=2, measurement_basis="projector")
        projected_group_basis(a, {}, (0, 0))


@pytest.mark.integration
def test_symbolic_all_center_transfer_bound_covers_actual_balanced_source() -> None:
    from benchmarks.eth.spectral_factor_width_probe import ring_formula

    formula = ring_formula(6, width=2)
    r, Q, R = 2, 2, 2
    ell = sum(map(len, formula.clauses))
    built = construct_bounded_designs(
        formula, r=r, Q=Q, R=R, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    bound = projected_transfer_gram_envelope(
        formula.nvars, ell, r=r, Q=Q, R=R,
    )
    assert bound.maximum_group_size_upper == 6
    assert bound.possible_group_copy_calls_upper == Q * r * ell
    assert len(built.centers) == Q
    for _, design in built.centers:
        assert max(map(len, design.groups)) <= bound.maximum_group_size_upper
        assert len(design.matrices) == r
        for group, rows in zip(design.groups, design.matrices):
            assert len(rows) <= ell * len(group)
            assert all(len(row) == len(group) for row in rows)
            assert all(
                max((abs(v).bit_length() for v in row), default=0)
                <= bound.per_call.primitive_basis_bits_upper
                for row in rows
            )
    assert bound.cumulative_abstract_bit_work_upper > 0
    assert bound.simultaneous_abstract_bit_storage_upper > 0


@pytest.mark.checkpoint
def test_paper_regime_symbolic_group_size_and_work_are_polynomial_expressions() -> None:
    n = 10 ** 100
    ell = 3 * n
    r, Q, R = 31, 20_000, 4_000
    bound = projected_transfer_gram_envelope(
        n, ell, r=r, Q=Q, R=R,
    )
    assert bound.possible_group_copy_calls_upper == Q * r * ell
    assert bound.maximum_group_size_upper * r >= 2 * n
    assert bound.maximum_group_size_upper * r < 2 * n + r
    assert bound.per_call.projector_query_count_upper == ell ** 2
    assert bound.per_call.transient_integer_bits_upper > 0
    assert bound.cumulative_abstract_bit_work_upper.bit_length() < 50_000
    assert bound.simultaneous_abstract_bit_storage_upper.bit_length() < 50_000
    with pytest.raises(ValueError):
        projected_transfer_gram_envelope(1, 2, r=2, Q=2, R=2)
