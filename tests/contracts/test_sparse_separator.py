"""Differential and structural checks for sparse separator contraction."""
from __future__ import annotations
import random
import unittest
from itertools import product
from non_exponential_sudoku.core.jets import JetRing
from non_exponential_sudoku.elimination.engine import ModeEliminator
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from tests.support.mode_factors import synthetic_modes, reference_factor_sum, dp_sum


def square_grid(side):
    return ([(y*side+x,y*side+x+1) for y in range(side) for x in range(side-1)] +
            [(y*side+x,(y+1)*side+x) for y in range(side-1) for x in range(side)])


def equal_factor(g,scope,bits,R):
    return R.one if len(set(bits)) <= 1 else R.zero


class SparseSeparatorTests(unittest.TestCase):
    def test_random_zero_support_matches_reference(self):
        rng=random.Random(22062026)
        for p in (3,6,10):
            B=Padic(5,modulus_polynomial(5),p)
            for edge_count in (2,4,6,8):
                for case in range(4):
                    pairs=[tuple(rng.sample(range(5),2)) for _ in range(edge_count)]
                    modes=synthetic_modes(pairs,p)
                    scopes={g:tuple(j for j,m in enumerate(modes) if g in (m.source,m.target))
                            for pair in pairs for g in pair}
                    tables={g:{b:B.scalar(rng.choice([0,0,0,1,2,5]))
                               for b in product((0,1), repeat=len(scope))}
                            for g,scope in scopes.items()}
                    def fn(g,scope,bits):return tables[g][bits]
                    expected=reference_factor_sum(modes,B,fn)
                    for order in ('min_fill','min_states'):
                        for join in ('enumerate','sparse','adaptive'):
                            got,stats=dp_sum(modes,B,fn,order=order,join_strategy=join)
                            self.assertEqual(got,expected,(p,edge_count,case,join))

    def test_connected_lattice_counts_without_full_enumeration(self):
        for side in (2,3,4):
            pairs=square_grid(side)
            B=Padic(5,modulus_polynomial(5),len(pairs)+3)
            modes=synthetic_modes(pairs,B.p)
            expected=B.scalar(2)
            for strategy in ('enumerate','sparse','adaptive'):
                got,stats=dp_sum(modes,B,
                     lambda g,sc,b:equal_factor(g,sc,b,B),
                     order='min_fill',join_strategy=strategy,
                     max_factor_states=10000,max_operations=3_000_000)
                self.assertEqual(got,expected,(side,strategy))
                if strategy=='sparse':self.assertGreater(stats.mode_dp_sparse_joins,0)

    def test_nested_jet_and_early_weight_pruning(self):
        B=Padic(5,modulus_polynomial(5),4)
        R=JetRing(JetRing(B,2),3)
        pairs=[(0,1),(1,2),(2,0),(2,3)]
        modes=synthetic_modes(pairs,R.p)
        def fn(g,sc,b):
            if sum(b)>1:return R.zero
            return R.add(R.scalar(g+1),R.variable)
        expected=reference_factor_sum(modes,R,fn)
        for join in ('enumerate','sparse','adaptive'):
            self.assertEqual(dp_sum(modes,R,fn,join_strategy=join)[0],expected)

    def test_sparse_join_refuses_oversize_without_fallback(self):
        R=Padic(5,modulus_polynomial(5),13)
        modes=synthetic_modes([(0,1)]*8,R.p)
        def fn(*args):return R.one
        with self.assertRaisesRegex(CapacityError,'(limit|work)'):
            dp_sum(modes,R,fn,join_strategy='sparse',max_factor_states=20)
        with self.assertRaisesRegex(CapacityError,'(limit|work)'):
            dp_sum(modes,R,fn,join_strategy='sparse',max_operations=15)

    def test_invalid_join_strategy_fails(self):
        R=Padic(5,modulus_polynomial(5),4)
        with self.assertRaises(ValueError):
            dp_sum(synthetic_modes([(0,1)],R.p),R,lambda *a:R.one,join_strategy='guess')



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.integration
