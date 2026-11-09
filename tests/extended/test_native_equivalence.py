"""Optional Cython ring must be bit-for-bit identical to reference arithmetic."""
from __future__ import annotations
import random
import unittest
from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig, Padic, modulus_polynomial
from non_exponential_sudoku.core import algebra as core_algebra

class NativeRingEquivalence(unittest.TestCase):
    @unittest.skipUnless(core_algebra._native_ring is not None, 'native_ring extension not built')
    def test_randomized_arithmetic(self):
        native = core_algebra._native_ring
        original = core_algebra._native_ring
        rng = random.Random(982713)
        try:
            for degree in (2, 5, 12, 32):
                for precision in (1, 3, 9, 63, 129, 521):
                    R=Padic(degree,modulus_polynomial(degree),precision)
                    for _ in range(8):
                        a=tuple(rng.randrange(1<<precision) for _ in range(degree))
                        b=tuple(rng.randrange(1<<precision) for _ in range(degree))
                        core_algebra._native_ring=None
                        ref=(R.add(a,b),R.sub(a,b),R.mul(a,b))
                        core_algebra._native_ring=original
                        got=(R.add(a,b),R.sub(a,b),R.mul(a,b))
                        self.assertEqual(got,ref, (degree,precision))
        finally:
            core_algebra._native_ring=original

    @unittest.skipUnless(core_algebra._native_ring is not None,'native_ring extension not built')
    def test_end_to_end_modes(self):
        from reference.real_sudoku_bench import puzzles
        from reference.local_support import pin_band_wires
        original=core_algebra._native_ring
        try:
            for name,puzzle,expected in puzzles():
                if name not in ('4x4-12-givens-two-solutions','9x9-77-givens-two-solutions'):
                    continue
                net,_=pin_band_wires(puzzle)
                results=[]
                for engine in (None,original):
                    core_algebra._native_ring=engine
                    solver=ContractionEngine(ContractorConfig(net.edges,net.edges+1,schedule='micro', leaf=LeafConfig(strategy='eliminate')))
                    results.append(solver.contract(net))
                self.assertEqual(results[0],results[1])
                self.assertEqual(results[0][0],expected)
        finally:
            core_algebra._native_ring=original



# One primary execution tier per module; pytest reports stable JUnit testcases.
import pytest
pytestmark = pytest.mark.extended
