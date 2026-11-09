"""Exact characteristic-zero (mod 2**p) root-of-unity interpolation tests."""
import random
import unittest
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from reference.cook_mertz_probe import primitive_odd_root, root_average_polynomial

class CMInterpolationTests(unittest.TestCase):
    def test_exact_odd_root_interpolation_in_existing_ring(self):
        rng=random.Random(534)
        for e,m in ((4,3),(4,5),(6,3),(6,7)):
            for p in (2,7,13):
                R=Padic(e,modulus_polynomial(e),p)
                omega=primitive_odd_root(R,m)
                for _ in range(4):
                    v=tuple(rng.randrange(1<<p) for _ in range(e))
                    x=tuple(rng.randrange(1<<p) for _ in range(e))
                    coefficients=[R.scalar(rng.randrange(1<<p)) for _ in range(m)]
                    target=R.zero
                    for c in reversed(coefficients):
                        target=R.add(R.mul(target,v),c)
                    self.assertEqual(root_average_polynomial(R,omega,m,v,x,coefficients),target)

    def test_rejects_unsupported_root_order(self):
        R=Padic(5,modulus_polynomial(5),9)
        with self.assertRaises(ValueError):primitive_odd_root(R,3)

    def test_aliasing_at_degree_m_is_real(self):
        R=Padic(4,modulus_polynomial(4),9)
        omega=primitive_odd_root(R,3)
        coeffs=[R.zero,R.zero,R.zero,R.one]
        # x^m survives averaging, so degree<m is necessary.
        at= root_average_polynomial(R,omega,3,R.zero,R.one,coeffs)
        self.assertEqual(at,R.one)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.checkpoint
