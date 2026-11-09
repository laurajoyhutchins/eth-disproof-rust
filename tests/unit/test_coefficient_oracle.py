"""Independent exact comparisons for a capped-cache coefficient oracle."""
import random
import unittest
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.core.lazy_coefficients import Expression, CoefficientOracle

class CoefficientOracleTest(unittest.TestCase):
    def test_random_rational_circuits_match_dense_exact_series(self):
        rng=random.Random(717)
        for nested in (False,True):
            base=Padic(5,modulus_polynomial(5),11)
            if nested:base=JetRing(base,3)
            q=6
            J=JetRing(base,q)
            for _ in range(5):
                a=[base.scalar(rng.randint(0,3)) for _ in range(q)]
                b=[base.scalar(rng.randint(0,3)) for _ in range(q)]
                a[0]=base.one
                b[0]=base.scalar(2)
                if nested:
                    a[2]=base.add(a[2],base.variable)
                A=Expression.coeffs(a);B=Expression.coeffs(b)
                expr=(A*B+A)*(A+B).inverse()
                expected=J.mul(J.add(J.mul(tuple(a),tuple(b)),tuple(a)),
                               J.inv(J.add(tuple(a),tuple(b))))
                for limit in (0,8,96):
                    got=CoefficientOracle(base,q,limit).series(expr)
                    self.assertEqual(got,expected)
    def test_shared_subexpression_recomputation_can_explode(self):
        base=Padic(5,modulus_polynomial(5),11)
        q=9
        x=Expression.coeffs((base.one,base.one))
        expr=x
        for _ in range(4):expr=expr*expr
        no_cache=CoefficientOracle(base,q,0)
        cached=CoefficientOracle(base,q,128)
        self.assertEqual(no_cache.series(expr),cached.series(expr))
        self.assertGreater(no_cache.misses,100*cached.misses)
        self.assertLessEqual(cached.max_cached,128)

    def test_coefficient_access_partial_and_cache_peak(self):
        base=Padic(5,modulus_polynomial(5),13)
        q=10;J=JetRing(base,q)
        a=(base.one,base.scalar(2),base.scalar(1))+(base.zero,)*(q-3)
        b=(base.one,base.scalar(3),base.scalar(1))+(base.zero,)*(q-3)
        A=Expression.coeffs(a);B=Expression.coeffs(b)
        expr=(A*B)*(A*B)
        expected=J.mul(J.mul(a,b),J.mul(a,b))
        no_cache=CoefficientOracle(base,q,0)
        tiny=CoefficientOracle(base,q,3)
        cached=CoefficientOracle(base,q,128)
        for v in (no_cache,tiny,cached):
            self.assertEqual(v.series(expr),expected)
            self.assertLessEqual(v.max_cached,v.cache_limit)
        self.assertGreater(no_cache.misses,cached.misses)
        self.assertLessEqual(tiny.max_cached,3)



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
