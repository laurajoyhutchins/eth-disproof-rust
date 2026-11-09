"""Exact Sudoku counting by independently contracted residual components.

Each choice for a cell occupies three (unit, digit) obligations. Two cells
interact only if at least one of their currently permitted choices uses the
same obligation. Connected components of this incidence relation have no
cross-component conflicts, so their exact completion counts multiply.

``static`` computes this partition once and runs the ordinary forward frontier
recurrence independently on each component. ``adaptive`` additionally
conditions on cell choices and recomputes the partition of *live* candidate
obligations. This second mode is a memoized branching recurrence, not the
nonbranching forward tensor contractor, and can cost more than it saves.

No solver, solution witness, or exhaustive-count fallback is invoked. Every
state, transition, incidence visit and estimated-state-memory limit refuses
explicitly. Python dictionaries and graph work have other memory overhead, so
the byte budget is only an estimate, not an RSS limit.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

from .frontier import FrontierCapacityError, FrontierLimits
from .state import prepare_residual
from .three_cnf import Puzzle

ComponentMode = Literal['static', 'adaptive']


@dataclass(frozen=True)
class ComponentLimits:
    frontier: FrontierLimits = FrontierLimits()
    max_graph_visits: int = 5_000_000
    max_recursive_cells: int = 256

    def __post_init__(self) -> None:
        if self.max_graph_visits < 1 or self.max_recursive_cells < 1:
            raise ValueError('Component limits must be positive')


@dataclass(frozen=True)
class ComponentStats:
    fixed_cells: int
    free_cells: int
    initial_components: int
    largest_initial_component: int
    conditional_splits: int
    peak_states: int
    memo_states: int
    transitions: int
    compatible_transitions: int
    graph_visits: int


@dataclass(frozen=True)
class ComponentResult:
    count: int
    stats: ComponentStats


class _Work:
    def __init__(self, side: int, limits: ComponentLimits) -> None:
        self.limits = limits
        self.bytes_per_state = 224 + 2 * ((3 * side * side + 7) // 8)
        self.graph_visits = 0
        self.transitions = 0
        self.compatible = 0
        self.peak_states = 0
        self.memo_states = 0
        self.conditional_splits = 0

    def visit(self) -> None:
        self.graph_visits += 1
        if self.graph_visits > self.limits.max_graph_visits:
            raise FrontierCapacityError('Component graph-visit limit')

    def transition(self, compatible: bool) -> None:
        self.transitions += 1
        if self.transitions > self.limits.frontier.max_transitions:
            raise FrontierCapacityError('Component transition limit')
        if compatible:
            self.compatible += 1

    def guard(self, retained: int, building: int = 0) -> None:
        if max(retained, building) > self.limits.frontier.max_states:
            raise FrontierCapacityError('Component state limit')
        if (retained + building) * self.bytes_per_state > self.limits.frontier.max_estimated_bytes:
            raise FrontierCapacityError('Component estimated-byte limit')
        self.peak_states = max(self.peak_states, retained, building)




def _partition(
    candidates: dict[int, tuple[int, ...]], work: _Work,
) -> tuple[tuple[int, ...], ...]:
    """Certified components of live candidate-obligation incidence graph."""
    cells = tuple(sorted(candidates))
    parent = {cell: cell for cell in cells}
    bit_owner: dict[int, int] = {}

    def find(cell: int) -> int:
        while parent[cell] != cell:
            parent[cell] = parent[parent[cell]]
            cell = parent[cell]
        return cell

    for cell in cells:
        for candidate in candidates[cell]:
            bits = candidate
            while bits:
                bit = bits & -bits
                bits ^= bit
                work.visit()
                previous = bit_owner.setdefault(bit, cell)
                parent[find(cell)] = find(previous)
    grouped: dict[int, list[int]] = {}
    for cell in cells:
        grouped.setdefault(find(cell), []).append(cell)
    return tuple(sorted((tuple(members) for members in grouped.values()),
                        key=lambda group: group[0]))


def _advance_forward(
    table: dict[int, int], candidates: tuple[int, ...],
    keep: int, work: _Work,
) -> dict[int, int]:
    """One exact, resource-accounted contraction step for a chosen cell."""
    output: dict[int, int] = {}
    for signature, multiplicity in table.items():
        for candidate in candidates:
            compatible = not signature & candidate
            work.transition(compatible)
            if not compatible:
                continue
            key = (signature | candidate) & keep
            if key in output:
                output[key] += multiplicity
            else:
                work.guard(len(table), len(output) + 1)
                output[key] = multiplicity
    return output


def _count_forward(
    cells: tuple[int, ...], options: dict[int, tuple[int, ...]], work: _Work,
) -> int:
    future = [0] * (len(cells) + 1)
    for pos in range(len(cells) - 1, -1, -1):
        mask = future[pos + 1]
        for candidate in options[cells[pos]]:
            mask |= candidate
        future[pos] = mask
    table: dict[int, int] = {0: 1}
    work.guard(len(table))
    for pos, cell in enumerate(cells):
        table = _advance_forward(table, options[cell], future[pos + 1], work)
        if not table:
            return 0
    return sum(table.values())


def _count_adaptive(
    cells: tuple[int, ...], options: dict[int, tuple[int, ...]], work: _Work,
) -> int:
    if len(cells) > work.limits.max_recursive_cells:
        raise FrontierCapacityError('Component recursion depth limit')
    indexed = tuple(options[cell] for cell in cells)
    cell_union: list[int] = []
    for choices in indexed:
        union = 0
        for candidate in choices:
            union |= candidate
        cell_union.append(union)
    memo: dict[tuple[int, int], int] = {}

    def recurse(remaining: int, occupied: int) -> int:
        if not remaining:
            return 1
        active: dict[int, tuple[int, ...]] = {}
        full_future = 0
        mask = remaining
        while mask:
            bit = mask & -mask
            mask ^= bit
            cell = bit.bit_length() - 1
            full_future |= cell_union[cell]
        occupied &= full_future
        key = remaining, occupied
        if key in memo:
            return memo[key]
        if len(memo) >= work.limits.frontier.max_states:
            raise FrontierCapacityError('Component state limit')
        work.guard(len(memo) + 1)
        # Reserve before descent so the budget includes all active stack frames.
        # Every recursive call removes cells, hence no cycle can read this
        # provisional value as an already-computed answer.
        memo[key] = 0
        work.memo_states += 1
        mask = remaining
        first_forced: int | None = None
        while mask:
            bit = mask & -mask
            mask ^= bit
            cell = bit.bit_length() - 1
            valid = tuple(choice for choice in indexed[cell]
                          if not (choice & occupied))
            if not valid:
                return 0
            active[cell] = valid
            if len(valid) == 1 and first_forced is None:
                first_forced = cell

        if first_forced is not None:
            chosen = first_forced
            choice = active[chosen][0]
            work.transition(True)
            result = recurse(remaining ^ (1 << chosen), occupied | choice)
        else:
            groups = _partition(active, work)
            if len(groups) > 1:
                work.conditional_splits += 1
                result = 1
                for group in groups:
                    component_mask = 0
                    for cell in group:
                        component_mask |= 1 << cell
                    result *= recurse(component_mask, occupied)
                    if result == 0:
                        break
            else:
                chosen = min(active)
                result = 0
                for choice in active[chosen]:
                    work.transition(True)
                    result += recurse(remaining ^ (1 << chosen), occupied | choice)
        memo[key] = result
        return result

    return recurse((1 << len(cells)) - 1, 0)


def count_components(
    puzzle: Puzzle, *, mode: ComponentMode = 'static',
    limits: ComponentLimits = ComponentLimits(),
    domains: Sequence[int] | None = None,
) -> ComponentResult:
    """Count completions by certified independent components.

    ``domains`` means count solutions *restricted* to those candidate sets;
    it does not claim that arbitrary restrictions preserve the original count.
    With ``mode='adaptive'``, the branch recursion is exact but may be slower
    than ordinary forward frontier counting on connected residual graphs.
    """
    if mode not in ('static', 'adaptive'):
        raise ValueError('Unknown component counting mode')
    options, satisfiable = prepare_residual(puzzle, domains)
    if not satisfiable:
        return ComponentResult(0, ComponentStats(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
    work = _Work(puzzle.side, limits)
    groups = _partition(options, work)
    result = 1
    for cells in groups:
        if mode == 'static':
            result *= _count_forward(cells, options, work)
        else:
            result *= _count_adaptive(cells, options, work)
        if result == 0:
            break
    return ComponentResult(result, ComponentStats(
        fixed_cells=len(puzzle.entries) - len(options),
        free_cells=len(options),
        initial_components=len(groups),
        largest_initial_component=max((len(x) for x in groups), default=0),
        conditional_splits=work.conditional_splits,
        peak_states=work.peak_states,
        memo_states=work.memo_states,
        transitions=work.transitions,
        compatible_transitions=work.compatible,
        graph_visits=work.graph_visits,
    ))
