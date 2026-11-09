"""Public Python ABI for optional native_sparse.pyx."""
from non_exponential_sudoku.elimination.factors import Factor
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.core.jets import NestedRing
from collections.abc import Sequence
from non_exponential_sudoku.runtime.statistics import Counters
from non_exponential_sudoku.runtime.budget import ModeBudget
def join_factors_sparse(factors: list[Factor], modes: Sequence[Mode], ring: NestedRing, budget: ModeBudget, stats: Counters) -> Factor: ...
def eliminate_one_sparse(var: int, incident: list[Factor], modes: Sequence[Mode], ring: NestedRing, budget: ModeBudget, stats: Counters) -> Factor: ...
