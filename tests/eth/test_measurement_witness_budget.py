"""Exact witness bit-work ceiling against production Gauss-Jordan and real spectra."""
from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

from non_exponential_sudoku.eth.cnf import CNFFormula
from non_exponential_sudoku.eth.construction import construct_bounded_designs
from non_exponential_sudoku.eth.design import _row_combination, certify_measurements
from reference.eth_measurement_witness_budget import (
    traced_row_combination, witness_bit_budget,
)


@pytest.mark.checkpoint
def test_2100_seeded_rectangular_witnesses_preserve_exact_source_solution() -> None:
    rng = Random(963951)
    for _ in range(2100):
        width, count = rng.randrange(0, 9), rng.randrange(0, 9)
        rows = tuple(
            tuple(rng.randrange(-100, 101) for _ in range(width))
            for _ in range(count)
        )
        true_coefficients = tuple(
            Fraction(rng.randrange(-500, 501), rng.randrange(1, 100))
            for _ in range(count)
        )
        target = tuple(
            sum((weight * row[j] for weight, row in zip(true_coefficients, rows)),
                Fraction(0))
            for j in range(width)
        )
        envelope = witness_bit_budget(rows, target)
        traced = traced_row_combination(rows, target)
        assert traced.coefficients == _row_combination(rows, target)
        assert traced.measured_fraction_bits <= envelope.intermediate_fraction_bits_upper
        assert traced.measured_rational_operations <= envelope.rational_operations_upper
        assert envelope.retained_fraction_slots_upper >= width * (count + 1)


@pytest.mark.checkpoint
def test_empty_inconsistent_and_nonlinear_input_types_fail_without_false_receipt() -> None:
    assert _row_combination(((), ()), ()) == (Fraction(0), Fraction(0))
    assert traced_row_combination(((), ()), ()).coefficients == (
        Fraction(0), Fraction(0),
    )
    for rows, target in (
        (((0, 0),), (Fraction(0), Fraction(1))),
        ((), (Fraction(2),)),
    ):
        witness_bit_budget(rows, target)
        with pytest.raises(ValueError, match="outside measurement row space"):
            traced_row_combination(rows, target)
        with pytest.raises(ValueError, match="outside measurement row space"):
            _row_combination(rows, target)
    with pytest.raises(ValueError, match="width mismatch"):
        witness_bit_budget(((1, 0),), (Fraction(1),))
    with pytest.raises(ValueError, match="exact integers"):
        witness_bit_budget(((True,),), (Fraction(1),))
    with pytest.raises(ValueError, match="exact rational"):
        witness_bit_budget(((1,),), (0.25,))


@pytest.mark.integration
def test_actual_implicit_spectral_measurement_witnesses_fit_bit_budget() -> None:
    # Source conditional schedules, exact spectral transfer, and projector
    # measurement rows, not arbitrary integer matrices or handwritten basis.
    # The small fixture is intentionally NOT Step-5 admitted.
    formula = CNFFormula(4, ((1, 2), (-2, 3), (3, 4), (-4, 1)))
    construction = construct_bounded_designs(
        formula, r=2, Q=2, R=2, schedule="conditional",
        representation="implicit", measurement_basis="projector",
    )
    assert construction.paper_admission is not None
    assert not construction.paper_admission.admitted
    checked = 0
    for center, design in construction.centers:
        certificate = certify_measurements(
            formula, construction.replacements, design, at=center,
        )
        for e, (forms, witnesses) in enumerate(zip(
            construction.replacements.clauses, certificate.occurrences,
        )):
            owner = design.clause_groups[e]
            for form, witness in zip(forms, witnesses):
                for g, (group, rows) in enumerate(zip(
                    design.groups, design.matrices,
                )):
                    if g == owner:
                        continue
                    target = tuple(
                        form.coefficients[v].evaluate(center) for v in group
                    )
                    envelope = witness_bit_budget(rows, target)
                    trace = traced_row_combination(rows, target)
                    assert trace.coefficients == witness.lambda_by_group[g]
                    assert trace.measured_fraction_bits <= (
                        envelope.intermediate_fraction_bits_upper
                    )
                    assert trace.measured_rational_operations <= (
                        envelope.rational_operations_upper
                    )
                    checked += 1
    assert checked == 2 * sum(map(len, formula.clauses))
