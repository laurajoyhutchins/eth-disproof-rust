"""Exact coefficient arithmetic does not depend on a Sudoku search engine."""
import pytest
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial

pytestmark = pytest.mark.checkpoint


@pytest.mark.parametrize('degree,precision', [(2, 3), (3, 5), (4, 7)])
def test_quotient_ring_identities(degree: int, precision: int) -> None:
    ring = Padic(degree, modulus_polynomial(degree), precision)
    a = ring.lift(range(1, degree + 1))
    b = ring.lift(range(2, degree + 2))
    assert ring.mul(a, ring.one) == a
    assert ring.mul(a, b) == ring.mul(b, a)
    assert ring.add(a, ring.neg(a)) == ring.zero
