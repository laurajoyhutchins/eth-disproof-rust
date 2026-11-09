"""Independent-facing optional FLINT adapter for exact quotient-ring tests.

The implementation is shared with the opt-in production backend, so use
SymPy and the pure-Python Padic path as *independent* correctness references.
"""
from __future__ import annotations

from non_exponential_sudoku.core.flint_backend import FlintRingArithmetic as FlintRingOracle

__all__ = ["FlintRingOracle"]
