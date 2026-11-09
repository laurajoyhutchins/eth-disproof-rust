"""External backend boundary contracts and opt-in native differential tests."""
from __future__ import annotations

from fractions import Fraction
from random import Random
from types import SimpleNamespace

import pytest

from non_exponential_sudoku.eth import (
    BackendUnavailableError, CNFFormula, HermiteDatum, MeasurementDesign,
    Polynomial, count_bruteforce, count_from_manual_designs, count_ganak,
    deformation_polynomial, interpolate_hermite, taylor_coefficients_separated,
)
from non_exponential_sudoku.eth.backends import (
    flint_polynomial_op, flint_row_combination, flint_taylor,
)
from non_exponential_sudoku.eth.design import _row_combination
from non_exponential_sudoku.runtime.budget import CapacityError

pytestmark = pytest.mark.checkpoint


def coordinate_design(nvars: int, count: int) -> MeasurementDesign:
    groups = (tuple(range(nvars)),)
    return MeasurementDesign(
        groups, (0,) * count,
        (tuple(tuple(int(i == j) for i in range(nvars)) for j in range(nvars)),),
        Fraction(1), 1 if nvars else 0,
    )


def test_ganak_mock_contract_preserves_unused_variables_and_exact_int(monkeypatch: pytest.MonkeyPatch) -> None:
    import non_exponential_sudoku.eth.ganak as ganak

    seen: list[object] = []

    class Counter:
        def __init__(self, *, seed: int = 0) -> None:
            seen.append(('seed', seed))

        def new_vars(self, nvars: int) -> None:
            seen.append(('nvars', nvars))

        def add_clauses(self, clauses: list[list[int]]) -> None:
            seen.append(('clauses', clauses))

        def count(self) -> int:
            return 8

    monkeypatch.setattr(ganak, 'import_module', lambda _: SimpleNamespace(Counter=Counter))
    assert count_ganak(CNFFormula(4, ((1,),)), seed=7) == 8
    assert seen == [('seed', 7), ('nvars', 4), ('clauses', [[1]])]
    # Both identities are handled before loading the native extension.
    assert count_ganak(CNFFormula(8, ())) == 256
    assert count_ganak(CNFFormula(8, ((),))) == 0
    with pytest.raises(CapacityError, match='declared-variable'):
        count_ganak(CNFFormula(3, ()), max_variables=2)
    with pytest.raises(ValueError, match='max_variables'):
        count_ganak(CNFFormula(1, ()), max_variables=-1)
    with pytest.raises(ValueError, match='uint64'):
        count_ganak(CNFFormula(1, ((1,),)), seed=-1)


def test_ganak_invalid_output_and_missing_dependency_fail_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    import non_exponential_sudoku.eth.ganak as ganak

    class Counter:
        def __init__(self, **_: object) -> None:
            pass

        def new_vars(self, _: int) -> None:
            pass

        def add_clauses(self, _: list[list[int]]) -> None:
            pass

        def count(self) -> float:
            return 1.0

    monkeypatch.setattr(ganak, 'import_module', lambda _: SimpleNamespace(Counter=Counter))
    with pytest.raises(ArithmeticError, match='invalid exact'):
        count_ganak(CNFFormula(1, ((1,),)))

    def missing(_: str) -> None:
        raise ImportError('not installed')

    monkeypatch.setattr(ganak, 'import_module', missing)
    with pytest.raises(BackendUnavailableError, match='pyganak'):
        count_ganak(CNFFormula(1, ((1,),)))


def test_missing_flint_is_not_silently_emulated(monkeypatch: pytest.MonkeyPatch) -> None:
    import non_exponential_sudoku.eth.backends as backends

    def missing(_: str) -> None:
        raise ImportError('not installed')

    monkeypatch.setattr(backends, 'import_module', missing)
    with pytest.raises(BackendUnavailableError, match='python-flint'):
        Polynomial((1, 2)).taylor(1, 2, backend='flint')
    with pytest.raises(BackendUnavailableError, match='python-flint'):
        taylor_coefficients_separated(CNFFormula(1, ((1,),)), coordinate_design(1, 1),
                                      at=1, order=0, backend='flint')
    with pytest.raises(ValueError, match='unknown'):
        Polynomial((1, 2)).taylor(1, 2, backend='unknown')  # type: ignore[arg-type]


def test_flint_external_polynomial_and_row_space_exactness() -> None:
    pytest.importorskip('flint')
    rng = Random(2608)
    for _ in range(40):
        a = tuple(Fraction(rng.randint(-10, 10), rng.randint(1, 10)) for _ in range(4))
        b = tuple(Fraction(rng.randint(-10, 10), rng.randint(1, 10)) for _ in range(3))
        left, right = Polynomial(a), Polynomial(b)
        assert Polynomial(flint_polynomial_op('add', a, b)) == left + right
        assert Polynomial(flint_polynomial_op('sub', a, b)) == left - right
        assert Polynomial(flint_polynomial_op('mul', a, b)) == left * right
        assert Polynomial(flint_polynomial_op('mul', a, b, max_length=3)) == (left * right).truncate(2)
        center = Fraction(rng.randint(-4, 4), 3)
        assert Polynomial(flint_taylor(a, center, 2)) == left.taylor(center, 2)
    for rows, target in (
        (((1, 2), (2, 4)), (Fraction(3), Fraction(6))),
        (((1, 0), (0, 1)), (Fraction(1, 3), Fraction(-2, 5))),
        (((0, 0),), (Fraction(0), Fraction(0))),
        ((), (Fraction(0),)),
    ):
        assert flint_row_combination(rows, target) == _row_combination(rows, target)
    with pytest.raises(ValueError, match='row space'):
        flint_row_combination(((1, 2),), (Fraction(1), Fraction(3)))


def test_flint_external_end_to_end_matches_reference() -> None:
    pytest.importorskip('flint')
    for formula in (CNFFormula(2, ((1, -2),)), CNFFormula(2, ()),
                    CNFFormula(2, ((),)), CNFFormula(2, ((1,), (-1,)))):
        design = coordinate_design(formula.nvars, len(formula.clauses))
        assert deformation_polynomial(formula, backend='flint') == deformation_polynomial(formula)
        for order in (0, 1):
            flint = taylor_coefficients_separated(formula, design, at=1, order=order, backend='flint')
            python = taylor_coefficients_separated(formula, design, at=1, order=order)
            assert flint.coefficients == python.coefficients
        actual = count_from_manual_designs(formula, ((1, design),), order=0, backend='flint')
        assert actual.count == count_bruteforce(formula)
    poly = Polynomial((Fraction(2, 3), Fraction(4, 7), Fraction(5, 11)))
    data = [HermiteDatum(Fraction(c), poly.taylor(c, 1).coefficients) for c in (1, 2)]
    assert interpolate_hermite(data, degree_bound=2, backend='flint').polynomial == poly


def test_ganak_external_differential() -> None:
    pytest.importorskip('pyganak')
    rng = Random(10026)
    for _ in range(450):
        n = rng.randint(0, 8)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(0, 3)))
                        for _ in range(rng.randint(0, 10))) if n else tuple(() for _ in range(rng.randint(0, 3)))
        formula = CNFFormula(n, clauses)
        assert count_ganak(formula) == count_bruteforce(formula)



def test_ganak_external_preserves_declared_unused_variables_and_big_counts() -> None:
    pytest.importorskip('pyganak')
    # Unconstrained variables must multiply the exact count by powers of 2.
    # In particular this exceeds machine-word precision on supported machines.
    for n in (1, 9, 31, 80, 120):
        formula = CNFFormula(n, ((1,),))
        assert count_ganak(formula) == 1 << (n - 1)
    assert count_ganak(CNFFormula(7, ((1,), (-1,)))) == 0
    assert count_ganak(CNFFormula(7, ((),))) == 0
    assert count_ganak(CNFFormula(7, ())) == 1 << 7


def test_flint_protocol_wiring_with_independent_sympy_matrix(monkeypatch: pytest.MonkeyPatch) -> None:
    """Simulated FLINT protocol exercises selection; NOT native verification."""
    sympy = pytest.importorskip('sympy')
    import non_exponential_sudoku.eth.backends as backends
    from non_exponential_sudoku.eth.polynomial import ReplacementForm, ReplacementSystem

    class MockPoly:
        def __init__(self, coefficients: list[Fraction] | tuple[Fraction, ...]) -> None:
            self.poly = Polynomial(tuple(coefficients))

        def __add__(self, other: MockPoly) -> MockPoly:
            return MockPoly((self.poly + other.poly).coefficients)

        def __sub__(self, other: MockPoly) -> MockPoly:
            return MockPoly((self.poly - other.poly).coefficients)

        def __mul__(self, other: MockPoly) -> MockPoly:
            return MockPoly((self.poly * other.poly).coefficients)

        def __neg__(self) -> MockPoly:
            return MockPoly((-self.poly).coefficients)

        def truncate(self, length: int) -> MockPoly:
            return MockPoly(self.poly.truncate(length - 1).coefficients)

        def coeffs(self) -> list[Fraction]:
            return list(self.poly.coefficients)

        def __len__(self) -> int:
            return len(self.poly.coefficients) if self.poly != Polynomial.constant(0) else 0

        def __bool__(self) -> bool:
            return self.poly != Polynomial.constant(0)

        def __getitem__(self, index: int) -> Fraction:
            return self.poly.coefficients[index] if index < len(self.poly.coefficients) else Fraction(0)

    mockflint = SimpleNamespace(
        fmpq=lambda numerator, denominator: Fraction(numerator, denominator),
        fmpq_poly=MockPoly,
        fmpq_mat=lambda rows: sympy.Matrix(rows),
    )
    monkeypatch.setattr(backends, 'import_module', lambda name: mockflint)
    formula = CNFFormula(2, ((1, -2),))
    design = coordinate_design(2, len(formula.clauses))
    identity = ReplacementSystem.identity(formula)
    transformed = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
        poly + Polynomial((0, Fraction(index + 1, 3)))
        for index, poly in enumerate(form.coefficients))) for form in rows)
        for rows in identity.clauses))
    direct = deformation_polynomial(formula, transformed)
    assert deformation_polynomial(formula, transformed, backend='flint') == direct
    for order in (0, 1, 2):
        got = taylor_coefficients_separated(formula, design, transformed,
                                            at=Fraction(2, 3), order=order, backend='flint')
        ref = direct.taylor(Fraction(2, 3), order)
        assert got.coefficients == ref.coefficients + (Fraction(0),) * (order + 1 - len(ref.coefficients))
    # Enough Hermite data from one nonzero center to recover the degree-two polynomial.
    counted = count_from_manual_designs(formula, ((Fraction(1), design),), transformed,
                                        order=direct.degree, backend='flint')
    assert counted.count == count_bruteforce(formula)
    # Cross-group row-space witness uses the exact sympy matrix RREF mock.
    rows = ((1, 2), (2, 4))
    assert flint_row_combination(rows, (Fraction(3), Fraction(6))) == (3, 0)


def test_flint_external_randomized_rational_polynomials() -> None:
    """Real binary FLINT, including zero polynomials and truncated products."""
    pytest.importorskip('flint')
    rng = Random(20261108)
    for _ in range(240):
        a = tuple(Fraction(rng.randint(-100, 100), rng.randint(1, 40))
                  for _ in range(rng.randrange(0, 25)))
        b = tuple(Fraction(rng.randint(-100, 100), rng.randint(1, 40))
                  for _ in range(rng.randrange(0, 25)))
        left, right = Polynomial(a), Polynomial(b)
        for operation, expected in (('add', left + right), ('sub', left - right),
                                    ('mul', left * right)):
            assert Polynomial(flint_polynomial_op(operation, a, b)) == expected
        length = rng.randint(1, 22)
        assert Polynomial(flint_polynomial_op('mul', a, b, max_length=length)) == (
            left * right).truncate(length - 1)
        center = Fraction(rng.randint(-30, 30), rng.randint(1, 20))
        order = rng.randint(0, 8)
        assert Polynomial(flint_taylor(a, center, order)) == left.taylor(center, order)


def test_flint_external_randomized_row_space_witnesses() -> None:
    """Exact RREF certificates and refusals for rectangular/rank-deficient matrices."""
    pytest.importorskip('flint')
    rng = Random(20261109)
    for _ in range(500):
        width, nrows = rng.randrange(0, 7), rng.randrange(0, 7)
        rows = tuple(tuple(rng.randint(-3, 3) for _ in range(width))
                     for _ in range(nrows))
        coefficients = tuple(Fraction(rng.randint(-5, 5), rng.randint(1, 7))
                             for _ in range(nrows))
        target = tuple(sum((rows[j][i] * coefficients[j] for j in range(nrows)),
                           Fraction(0)) for i in range(width))
        witness = flint_row_combination(rows, target)
        assert witness == _row_combination(rows, target)
        assert all(sum((witness[j] * rows[j][i] for j in range(nrows)),
                       Fraction(0)) == target[i] for i in range(width))
        if width:
            changed = list(target)
            changed[rng.randrange(width)] += Fraction(1, 7)
            try:
                ref = _row_combination(rows, tuple(changed))
            except ValueError:
                with pytest.raises(ValueError, match='row space'):
                    flint_row_combination(rows, tuple(changed))
            else:
                assert flint_row_combination(rows, tuple(changed)) == ref


def test_flint_external_randomized_hermite_reconstruction() -> None:
    """Mixed-order nonzero-center Hermite data over exact Q."""
    pytest.importorskip('flint')
    rng = Random(20261110)
    for _ in range(80):
        degree = rng.randint(0, 8)
        polynomial = Polynomial(tuple(Fraction(rng.randint(-10, 10), rng.randint(1, 7))
                                      for _ in range(degree + 1)))
        centers = rng.sample((*range(-8, 0), *range(1, 9)), rng.randint(1, 4))
        orders = [rng.randint(0, 4) for _ in centers]
        while sum(order + 1 for order in orders) <= degree:
            orders[rng.randrange(len(orders))] += 1
        data = tuple(HermiteDatum(Fraction(c), polynomial.taylor(c, order).coefficients +
                                  (Fraction(0),) * (
                                      order + 1 - len(polynomial.taylor(c, order).coefficients)))
                     for c, order in zip(centers, orders))
        assert interpolate_hermite(data, degree_bound=degree, backend='flint').polynomial == polynomial
        assert interpolate_hermite(data, degree_bound=degree, backend='python').polynomial == polynomial


def test_flint_external_randomized_full_taylor_count() -> None:
    """Real FLINT: deformed H, separated jets, and exact manual-design #SAT."""
    pytest.importorskip('flint')
    from non_exponential_sudoku.eth.polynomial import ReplacementForm, ReplacementSystem

    rng = Random(20261111)
    for _ in range(30):
        n = rng.randint(1, 4)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(1, 3)))
                        for _ in range(rng.randint(0, 4)))
        formula = CNFFormula(n, clauses)
        identity = ReplacementSystem.identity(formula)
        forms = ReplacementSystem(tuple(tuple(ReplacementForm(tuple(
            poly + Polynomial((0, Fraction(rng.randint(-2, 2), rng.randint(1, 4))))
            for poly in form.coefficients)) for form in row) for row in identity.clauses))
        direct = deformation_polynomial(formula, forms)
        assert deformation_polynomial(formula, forms, backend='flint') == direct
        # A one-group, zero-measurement certificate is valid but does not
        # claim any algorithmic speedup. It exercises every Taylor stage.
        design = MeasurementDesign((tuple(range(n)),), (0,) * len(formula.clauses),
                                   ((),), Fraction(0), 0)
        for order in (0, 1, 2):
            native = taylor_coefficients_separated(formula, design, forms,
                                                   at=Fraction(2, 3), order=order,
                                                   backend='flint')
            reference = direct.taylor(Fraction(2, 3), order)
            assert native.coefficients == reference.coefficients + (
                (Fraction(0),) * (order + 1 - len(reference.coefficients)))
        upper_bound = sum(sum(max((p.degree for p in f.coefficients), default=0)
                              for f in row) for row in forms.clauses)
        result = count_from_manual_designs(formula, ((Fraction(2, 3), design),),
                                           forms, order=upper_bound, backend='flint')
        assert result.count == count_bruteforce(formula)
        assert result.polynomial == direct
