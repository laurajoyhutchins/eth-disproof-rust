"""Source-constrained Boolean input oracles for the direct Sudoku reduction.

These immutable, finite-program callables replace opaque per-vertex closures.
They check a fixed number of Boolean input wires and return ONE scalar 0/1
in the supplied ring. They do not implement a Sudoku search or enumerate
candidate assignments. For a uniform abstract cost model see
reference/sudoku_oracle_cost.py.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..core.lazy_coefficients import NestedCoords
from ..core.network import TensorRing


def _validate_assignment(bits: tuple[int, ...], expected: int) -> None:
    if (len(bits) != expected or
            any(bit not in (0, 1, False, True) for bit in bits)):
        raise ValueError("Non-Boolean port")


def _decode(bits: tuple[int, ...], start: int, width: int) -> int:
    """Decode exactly width bits; all inputs were validated at the boundary."""
    value = 0
    for offset in range(width):
        value |= int(bits[start + offset]) << offset
    return value


def _validate_shape(side: int, width: int) -> None:
    if (type(side) is not int or side < 1 or
            type(width) is not int or
            width != max(1, (side - 1).bit_length())):
        raise ValueError("Invalid Sudoku oracle shape")


@dataclass(frozen=True, slots=True)
class CellEntryOracle:
    side: int
    width: int
    clue: int

    def __post_init__(self) -> None:
        _validate_shape(self.side, self.width)
        if type(self.clue) is not int or not 0 <= self.clue <= self.side:
            raise ValueError("Invalid Sudoku clue")

    def __call__(self, bits: tuple[int, ...], ring: TensorRing) -> NestedCoords:
        width = self.width
        _validate_assignment(bits, 3 * width)
        a = _decode(bits, 0, width)
        b = _decode(bits, width, width)
        c = _decode(bits, 2 * width, width)
        valid = (a == b == c and a < self.side
                 and (self.clue == 0 or self.clue == a + 1))
        return ring.scalar(int(valid))


@dataclass(frozen=True, slots=True)
class UnitEntryOracle:
    side: int
    width: int

    def __post_init__(self) -> None:
        _validate_shape(self.side, self.width)

    def __call__(self, bits: tuple[int, ...], ring: TensorRing) -> NestedCoords:
        width = self.width
        _validate_assignment(bits, self.side * width)

        # Bitset index is at most 2**width-1; therefore the accumulator
        # uses at most 2**width<=2*side bits, with no hashing assumption.
        # We deliberately do NOT reject a digit >=side here. The independent
        # direct-network unit tensor enforces only all-distinctness; the
        # cell tensor is responsible for checking the digit domain.
        seen = 0
        for start in range(0, len(bits), width):
            value = _decode(bits, start, width)
            mask = 1 << value
            if seen & mask:
                return ring.scalar(0)
            seen |= mask
        return ring.scalar(1)
