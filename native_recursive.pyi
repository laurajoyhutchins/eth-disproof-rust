"""Public Python ABI for optional native_recursive.pyx."""
from collections.abc import Sequence
from non_exponential_sudoku.core.network import Network, TensorRing, LeafPlan
from non_exponential_sudoku.core.lazy_coefficients import NestedCoords
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.core.algebra import RingCoords
def packet_evaluate(bits: tuple[int, ...], ring: TensorRing, left_positions: tuple[int, ...], row_cauchy: tuple[tuple[tuple[int, NestedCoords], ...], ...], contributions: tuple[tuple[tuple[int, NestedCoords], ...], ...], desired: tuple[int, ...], tile_slots: tuple[tuple[Mode, int, tuple[tuple[int, int], ...]], ...], right_positions: tuple[tuple[int, int], ...]) -> NestedCoords: ...
def eliminate_leaf(net: Network, R: TensorRing, max_edges: int = ..., max_width: int = ..., *, plan: LeafPlan | None = ..., max_factor_bytes: int | None = ...) -> NestedCoords: ...
