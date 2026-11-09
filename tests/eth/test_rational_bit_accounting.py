"""Unit and differential tests for witnessed operand-dependent bit accounting."""
from __future__ import annotations

import sys
from fractions import Fraction

import pytest

from benchmarks.eth.rational_bit_accounting import (
    _IntegerSteps, _replay, trace_fraction_bit_work,
)


@pytest.mark.checkpoint
@pytest.mark.parametrize("kind", ("_add", "_sub", "_mul", "_div"))
def test_reference_replay_exactly_matches_native_fractions(kind: str) -> None:
    cases = (
        (Fraction(3, 7), Fraction(5, 11)),
        (Fraction(-123, 55), Fraction(77, 21)),
        (Fraction(0, 7), Fraction(-9, 5)),
        (Fraction(10**45 + 7, 10**31 + 3),
         Fraction(-(10**39 + 5), 10**29 + 1)),
    )
    for a, b in cases:
        w = _IntegerSteps()
        n, d = _replay(kind, a, b, w)
        expected = {
            "_add": lambda: a + b,
            "_sub": lambda: a - b,
            "_mul": lambda: a * b,
            "_div": lambda: a / b,
        }[kind]()
        assert (n, d) == (expected.numerator, expected.denominator)
        assert w.steps > 0
        assert w.gcds >= 1
        assert w.gcd_division_steps > 0
        assert w.peak_bits >= max(a.numerator.bit_length(),
                                  a.denominator.bit_length())


@pytest.mark.checkpoint
def test_reference_accounting_is_operand_sensitive_not_max_bit_proxy() -> None:
    def small() -> Fraction:
        a, b = Fraction(1, 3), Fraction(2, 5)
        return (a + b) * (a - b)

    def big() -> Fraction:
        a = Fraction(10**90 + 17, 10**89 + 9)
        b = Fraction(10**88 + 7, 10**87 + 11)
        return (a + b) * (a - b)

    small_result, small_trace = trace_fraction_bit_work(small)
    big_result, big_trace = trace_fraction_bit_work(big)
    assert small_result != big_result
    a, b = small_trace.report(), big_trace.report()
    assert a["primitive_counts"]["_add"] == b["primitive_counts"]["_add"]
    assert a["primitive_counts"]["_mul"] == b["primitive_counts"]["_mul"]
    assert b["reference_schoolbook_bit_steps_upper_bound"] > (
        a["reference_schoolbook_bit_steps_upper_bound"] * 10)
    assert b["maximum_observed_input_component_bits"] > (
        a["maximum_observed_input_component_bits"])
    assert b["euclidean_gcd_division_steps"] > 0
    assert b["exact_result_replays_verified"] > 0
    assert b["bound_is_for_complete_algorithm"] is False
    assert b["bound_is_for_actual_CPython_machine_execution"] is False
    assert b["bare_integer_and_nonFraction_arithmetic_unaccounted"] is True
    assert sys.getprofile() is None


@pytest.mark.checkpoint
def test_trace_instrumentation_fails_closed_if_rational_hooks_unavailable() -> None:
    with pytest.raises(RuntimeError, match="internals unavailable"):
        trace_fraction_bit_work(lambda: 123)
    assert sys.getprofile() is None


@pytest.mark.integration
def test_ordered_benchmark_bit_trace_is_independent_and_exact() -> None:
    from benchmarks.eth.three_way_contraction import run_case

    result = run_case("path", 2, 1)
    for method in ("group-mask-elimination", "boolean-variable-elimination",
                   "tensor-jet"):
        arm = result["strategies"][method]
        assert arm["status"] == "exact"
        trace = arm["fraction_bit_accounting"]
        assert trace["status"] == "reference-arithmetic-bounded"
        assert trace["reference_schoolbook_bit_steps_upper_bound"] > 0
        assert trace["euclidean_gcd_calls"] > 0
        assert trace["integer_divisions"] >= trace["euclidean_gcd_division_steps"]
        assert trace["exact_result_replays_verified"] > 0
        assert trace["maximum_reference_intermediate_integer_bits"] > 0
        assert trace["uncovered_fraction_methods"] == {}
        assert trace["nonexact_constructors"] == 0
        assert "bit_work_proxy" not in arm


@pytest.mark.integration
def test_refused_evaluator_has_no_fabricated_bit_work_bound() -> None:
    from benchmarks.eth.three_way_contraction import run_case

    outcome = run_case("clique", 4, 1,
                       max_factor_entries=1, max_tensor_bond=1)
    assert all(arm["status"] == "refused"
               for arm in outcome["strategies"].values())
    assert all(arm["fraction_bit_accounting"]["status"] ==
               "not-measured-on-capacity-refusal"
               for arm in outcome["strategies"].values())
