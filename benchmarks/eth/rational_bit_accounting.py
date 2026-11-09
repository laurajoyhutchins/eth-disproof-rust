"""Witnessed rational bit accounting for the three exact ETH contractors.

A Python profiler records the REAL Fraction operands at every arithmetic
primitive in the execution, then independently replays the rational
algorithm through signed integer operations. Each integer operation is
charged a constructive schoolbook BIT-STEP UPPER BOUND depending on its
actual operand widths. Euclidean gcd is replayed division-by-division;
normalization and intermediate integer growth are included.

Scope is exactly the Fraction arithmetic trace, including measurement
certification and rank reduction. It is NOT a whole-program bit bound,
an empirical count of CPython machine instructions, or an upper bound
on an unexecuted/nonadmitted input. Bare integer operations elsewhere,
allocation, Python dispatch, hashing and GC are not covered. Unlike
the old max_bits**2 * logical_operation_count, each charged primitive
has actual input values and a checkable exact integer result.

Reference bit machine: integer addition <= 4*(max(a,b)+1) bit steps;
schoolbook multiplication <= 8*(a+1)*(b+1); shift/subtract division
<= 64*(a+1)*(b+1), for actual operand bit lengths a,b. Each Euclidean
gcd iteration is charged as an integer division. These conservative
constants cover sign, carry, comparison and shifting. This is a
constructive upper bound for this specified reference arithmetic path,
NOT a claim about CPython's actual bigint implementation.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass, field
from fractions import Fraction
from types import FrameType
from typing import Any, Callable, TypeVar

_Result = TypeVar("_Result")


def _bits(x: int) -> int:
    return max(1, abs(x).bit_length())


@dataclass
class _IntegerSteps:
    steps: int = 0
    adds: int = 0
    multiplies: int = 0
    divisions: int = 0
    gcds: int = 0
    gcd_division_steps: int = 0
    peak_bits: int = 0

    def observe(self, *values: int) -> None:
        self.peak_bits = max(self.peak_bits, *(_bits(x) for x in values))

    def add(self, a: int, b: int) -> int:
        self.observe(a, b)
        self.adds += 1
        self.steps += 4 * (max(_bits(a), _bits(b)) + 1)
        out = a + b
        self.observe(out)
        return out

    def multiply(self, a: int, b: int) -> int:
        self.observe(a, b)
        self.multiplies += 1
        self.steps += 8 * (_bits(a) + 1) * (_bits(b) + 1)
        out = a * b
        self.observe(out)
        return out

    def divmod(self, a: int, b: int, *, in_gcd: bool = False) -> tuple[int, int]:
        if b == 0:
            raise ZeroDivisionError("instrumentation integer division by zero")
        self.observe(a, b)
        self.divisions += 1
        self.gcd_division_steps += int(in_gcd)
        self.steps += 64 * (_bits(a) + 1) * (_bits(b) + 1)
        q, r = divmod(a, b)
        self.observe(q, r)
        return q, r

    def divide(self, a: int, b: int) -> int:
        q, r = self.divmod(a, b)
        if r:
            raise ArithmeticError("reference normalization is not exact")
        return q

    def gcd(self, a: int, b: int) -> int:
        self.gcds += 1
        a, b = abs(a), abs(b)
        self.observe(a, b)
        while b:
            _, r = self.divmod(a, b, in_gcd=True)
            a, b = b, r
        return a

    def power(self, base: int, exponent: int) -> int:
        if exponent < 0:
            raise ValueError("negative integer power in reference model")
        value = 1
        while exponent:
            if exponent & 1:
                value = self.multiply(value, base)
            exponent >>= 1
            if exponent:
                base = self.multiply(base, base)
        return value


def _replay(kind: str, a: Fraction, b: Fraction,
            w: _IntegerSteps) -> tuple[int, int]:
    na, da, nb, db = a.numerator, a.denominator, b.numerator, b.denominator
    if kind in ("_add", "_sub"):
        if kind == "_sub":
            nb = -nb
        g = w.gcd(da, db)
        if g == 1:
            n = w.add(w.multiply(na, db), w.multiply(da, nb))
            d = w.multiply(da, db)
        else:
            s = w.divide(da, g)
            t = w.add(w.multiply(na, w.divide(db, g)), w.multiply(nb, s))
            g2 = w.gcd(t, g)
            if g2 == 1:
                n, d = t, w.multiply(s, db)
            else:
                n = w.divide(t, g2)
                d = w.multiply(s, w.divide(db, g2))
    elif kind in ("_mul", "_div"):
        if kind == "_div":
            if nb == 0:
                raise ZeroDivisionError("instrumentation rational zero divisor")
            nb, db = db, nb
        g1 = w.gcd(na, db)
        if g1 > 1:
            na, db = w.divide(na, g1), w.divide(db, g1)
        g2 = w.gcd(nb, da)
        if g2 > 1:
            nb, da = w.divide(nb, g2), w.divide(da, g2)
        n, d = w.multiply(na, nb), w.multiply(da, db)
        if d < 0:
            n, d = -n, -d
    else:
        raise AssertionError("unsupported rational arithmetic primitive")
    if d <= 0:
        raise ArithmeticError("reference denominator must be positive")
    return n, d


def _constructor(numerator: int, denominator: int,
                 w: _IntegerSteps) -> tuple[int, int]:
    if denominator == 0:
        raise ZeroDivisionError("instrumentation constructor zero denominator")
    g = w.gcd(numerator, denominator)
    n, d = w.divide(numerator, g), w.divide(denominator, g)
    return (n, d) if d > 0 else (-n, -d)


@dataclass
class FractionBitTrace:
    primitive_counts: dict[str, int] = field(default_factory=dict)
    uncovered_fraction_methods: dict[str, int] = field(default_factory=dict)
    nonexact_constructors: int = 0
    integers: _IntegerSteps = field(default_factory=_IntegerSteps)
    max_input_bits: int = 0
    verified_results: int = 0
    _pending: dict[int, tuple[int, int]] = field(default_factory=dict, repr=False)

    def _count(self, kind: str) -> None:
        self.primitive_counts[kind] = self.primitive_counts.get(kind, 0) + 1

    def profiler(self, frame: FrameType, event: str, value: Any) -> None:
        if frame.f_globals.get("__name__") != "fractions":
            return
        method = frame.f_code.co_name
        if event == "return":
            expected = self._pending.pop(id(frame), None)
            if expected is not None:
                if not isinstance(value, Fraction) or (
                    value.numerator, value.denominator
                ) != expected:
                    raise ArithmeticError(
                        "reference rational replay differs from native " + method
                    )
                self.verified_results += 1
            return
        if event != "call":
            return
        local = frame.f_locals
        if method in ("_add", "_sub", "_mul", "_div"):
            a, b = local.get("a"), local.get("b")
            if not isinstance(a, Fraction) or not isinstance(b, Fraction):
                raise ArithmeticError("fraction hook received nonexact operands")
            self._count(method)
            self.max_input_bits = max(
                self.max_input_bits, _bits(a.numerator), _bits(a.denominator),
                _bits(b.numerator), _bits(b.denominator))
            self._pending[id(frame)] = _replay(method, a, b, self.integers)
        elif method == "__new__":
            n, d = local.get("numerator"), local.get("denominator")
            if type(n) is int and type(d) is int:
                self._count("integer-pair-constructor")
                self._pending[id(frame)] = _constructor(n, d, self.integers)
            elif type(n) is int and d is None:
                self._count("integer-constructor")
                self._pending[id(frame)] = (n, 1)
                self.integers.observe(n)
            elif isinstance(n, Fraction) and d is None:
                self._count("rational-copy-constructor")
                self._pending[id(frame)] = (n.numerator, n.denominator)
            else:
                self.nonexact_constructors += 1
        elif method == "_richcmp":
            a, b = local.get("self"), local.get("other")
            if isinstance(a, Fraction) and isinstance(b, (int, Fraction)):
                self._count("rational-comparison")
                self.integers.multiply(a.numerator,
                                       b.denominator if isinstance(b, Fraction) else 1)
                self.integers.multiply(a.denominator,
                                       b.numerator if isinstance(b, Fraction) else b)
            else:
                self._uncovered(method)
        elif method == "__eq__":
            self._count("rational-equality")
            a, b = local.get("a"), local.get("b")
            if isinstance(a, Fraction):
                self.integers.observe(a.numerator, a.denominator)
                values = [a.numerator, a.denominator]
                if isinstance(b, Fraction):
                    self.integers.observe(b.numerator, b.denominator)
                    values.extend((b.numerator, b.denominator))
                elif isinstance(b, int):
                    values.append(b)
                # Two equality comparisons of signed integers, each
                # bounded by linear work in their actual operand widths.
                self.integers.steps += 8 * (
                    max(_bits(value) for value in values) + 1)
        elif method in ("__neg__", "__abs__", "__pos__"):
            self._count(method)
            a = local.get("a")
            if isinstance(a, Fraction):
                self.integers.observe(a.numerator, a.denominator)
                self.integers.steps += 4 * (
                    _bits(a.numerator) + _bits(a.denominator) + 2)
        elif method == "__pow__":
            a, b = local.get("a"), local.get("b")
            if isinstance(a, Fraction) and isinstance(b, (Fraction, int)) and (
                isinstance(b, int) or b.denominator == 1
            ):
                exponent = int(b)
                self._count("integer-exponent-rational-power")
                n, d = a.numerator, a.denominator
                if exponent < 0:
                    n, d, exponent = d, n, -exponent
                    if d == 0:
                        return
                self._pending[id(frame)] = _constructor(
                    self.integers.power(n, exponent),
                    self.integers.power(d, exponent), self.integers)
            else:
                self._uncovered(method)
        elif method in ("forward", "reverse", "_from_coprime_ints",
                        "__bool__", "numerator", "denominator",
                        "__lt__", "__le__", "__gt__", "__ge__"):
            # Wrapper / property read: arithmetic is accounted inside
            # _richcmp, _add, _mul, _sub or _div, never double-charged.
            return
        elif method == "__int__":
            self._count("rational-integer-conversion")
            value = local.get("a")
            if isinstance(value, Fraction):
                self.integers.divmod(value.numerator, value.denominator)
        elif method == "__index__":
            self._count("integer-index-conversion")
        elif method.startswith("_operator_fallbacks"):
            return
        else:
            # In particular Python's hash and formatting are outside this
            # rational arithmetic bound; report rather than silently hide.
            self._uncovered(method)

    def _uncovered(self, method: str) -> None:
        self.uncovered_fraction_methods[method] = (
            self.uncovered_fraction_methods.get(method, 0) + 1)

    def report(self) -> dict[str, Any]:
        w = self.integers
        return {
            "scope": "observed-Fraction-arithmetic-only",
            "reference_schoolbook_bit_steps_upper_bound": w.steps,
            "bound_is_for_actual_CPython_machine_execution": False,
            "bound_is_for_complete_algorithm": False,
            "observed_rational_method_calls": sum(self.primitive_counts.values()),
            "primitive_counts": dict(sorted(self.primitive_counts.items())),
            "maximum_observed_input_component_bits": self.max_input_bits,
            "maximum_reference_intermediate_integer_bits": w.peak_bits,
            "integer_adds": w.adds,
            "integer_multiplies": w.multiplies,
            "integer_divisions": w.divisions,
            "euclidean_gcd_calls": w.gcds,
            "euclidean_gcd_division_steps": w.gcd_division_steps,
            "exact_result_replays_verified": self.verified_results,
            "nonexact_constructors": self.nonexact_constructors,
            "uncovered_fraction_methods": dict(sorted(
                self.uncovered_fraction_methods.items())),
            "bare_integer_and_nonFraction_arithmetic_unaccounted": True,
        }


def trace_fraction_bit_work(evaluate: Callable[[], _Result]
                            ) -> tuple[_Result, FractionBitTrace]:
    """Separate untimed re-execution, exact operand trace, fail-closed hooks."""
    trace = FractionBitTrace()
    if sys.getprofile() is not None:
        raise RuntimeError("fraction trace requires unused profile hook")
    try:
        sys.setprofile(trace.profiler)
        result = evaluate()
    finally:
        sys.setprofile(None)
    if trace._pending:
        raise ArithmeticError("unverified Fraction arithmetic return frames")
    if not trace.primitive_counts.get("_add") or not trace.primitive_counts.get("_mul"):
        raise RuntimeError("Fraction arithmetic internals unavailable to profiler")
    if trace.nonexact_constructors:
        raise RuntimeError("Fraction constructor outside exact integer domain")
    if trace.uncovered_fraction_methods:
        raise RuntimeError(
            "unmodeled Fraction methods prevent complete rational trace: "
            + repr(trace.uncovered_fraction_methods)
        )
    return result, trace
