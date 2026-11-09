"""Exact counting by bounded separators or an obligation-boundary ordering.

For each unassigned cell, a candidate uses three (unit, digit) obligations.
Two cells are connected if *any* of their candidates use a common obligation.
This is a conservative conflict graph: deleting a vertex separator makes the
surviving components independent, even after fixing an assignment to the
separator. The count is therefore a sum of products of component counts.

Small separators are searched exhaustively under a bounded number of graph
probes. If none are profitable, ``auto`` runs the same exact forward recurrence
with a cheap structural ordering. That ordering greedily minimizes the number
of obligation bits exposed to both the processed and unprocessed cells.
It is a width heuristic, not a treewidth certificate or complexity guarantee.

The optional ``reachable`` mode probes sampled *reachable* frontier signatures
and chooses between the structurally narrowest candidate cells. It accounts
for probe work separately, and uses the same exact forward recurrence after
selecting each cell. Probe predictions are heuristic; the count is not.

The counting paths share state and transition budgets; the reachable-order
probe has an additional explicit work budget. A refusal never
silently changes the counting algorithm or invokes a SAT solver.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, islice, product
from math import prod
from typing import Literal, Sequence

from .components import (
    ComponentLimits, _Work, _advance_forward, _count_forward,
)
from .frontier import FrontierCapacityError, FrontierLimits
from .three_cnf import Puzzle
from .state import prepare_residual

StructuralMethod = Literal['auto', 'boundary', 'condition', 'reachable']


@dataclass(frozen=True)
class StructuralLimits:
    frontier: FrontierLimits = FrontierLimits()
    max_graph_visits: int = 1_000_000
    max_separator_cells: int = 2
    max_separator_probes: int = 4_000
    max_separator_assignments: int = 4_096
    max_order_evaluations: int = 100_000
    max_pilot_transitions: int = 1_000_000
    pilot_sample_states: int = 64
    pilot_candidate_cells: int = 12

    def __post_init__(self) -> None:
        if (self.max_graph_visits < 1 or self.max_separator_cells < 0
                or self.max_separator_probes < 1
                or self.max_separator_assignments < 1
                or self.max_order_evaluations < 1
                or self.max_pilot_transitions < 1
                or not 1 <= self.pilot_sample_states <= 4096
                or not 1 <= self.pilot_candidate_cells <= 256):
            raise ValueError('Invalid structural counting limits')


@dataclass(frozen=True)
class StructuralStats:
    fixed_cells: int
    free_cells: int
    conflict_edges: int
    initial_components: int
    separator_probes: int
    separator_search_complete: bool
    smallest_separator_size: int | None
    chosen_separator: tuple[int, ...]
    resulting_component_sizes: tuple[int, ...]
    considered_separator_assignments: int
    compatible_separator_assignments: int
    boundary_order_evaluations: int
    boundary_width_upper_bound: int
    peak_states: int
    transitions: int
    compatible_transitions: int
    graph_visits: int
    method_used: str
    pilot_evaluations: int = 0
    pilot_transitions: int = 0


@dataclass(frozen=True)
class StructuralResult:
    count: int
    stats: StructuralStats


@dataclass(frozen=True)
class _Plan:
    separator: tuple[int, ...]
    components: tuple[tuple[int, ...], ...]
    assignments: int
    proxy_cost: int


class _Planner:
    def __init__(self, options: dict[int, tuple[int, ...]],
                 limits: StructuralLimits, work: _Work) -> None:
        self.options = options
        self.limits = limits
        self.work = work
        self.cells = tuple(sorted(options))
        self.obligations: dict[int, int] = {}
        for cell, candidates in options.items():
            union = 0
            for candidate in candidates:
                union |= candidate
            self.obligations[cell] = union
        self.adjacency: dict[int, int] = {cell: 0 for cell in options}
        self.positions = {cell: index for index, cell in enumerate(self.cells)}
        self.edges = 0
        for index, cell in enumerate(self.cells):
            for other in self.cells[index + 1:]:
                self.work.visit()
                if self.obligations[cell] & self.obligations[other]:
                    self.adjacency[cell] |= 1 << self.positions[other]
                    self.adjacency[other] |= 1 << self.positions[cell]
                    self.edges += 1
        self.probes = 0
        self.order_evaluations = 0
        self.pilot_evaluations = 0
        self.pilot_transitions = 0

    def components(self, excluded: tuple[int, ...] = ()) -> tuple[tuple[int, ...], ...]:
        remaining = ((1 << len(self.cells)) - 1)
        for cell in excluded:
            remaining &= ~(1 << self.positions[cell])
        groups: list[tuple[int, ...]] = []
        while remaining:
            seed = remaining & -remaining
            remaining ^= seed
            pending = seed
            found = 0
            while pending:
                bit = pending & -pending
                pending ^= bit
                found |= bit
                self.work.visit()
                cell = self.cells[bit.bit_length() - 1]
                adjacent = self.adjacency[cell] & remaining
                remaining ^= adjacent
                pending |= adjacent
            groups.append(tuple(self.cells[i] for i in range(len(self.cells))
                                if found & (1 << i)))
        return tuple(groups)

    def rank_boundary_candidates(
        self, remaining: set[int], processed: int,
    ) -> list[tuple[int, int, int, int]]:
        """Rank candidate cells by projected prefix/suffix obligation width.

        Each tuple contains (width, stable tie-break, cell, future mask).
        Prefix/suffix unions make the evaluation linear in remaining cells.
        """
        ordered = sorted(remaining)
        left = [0] * (len(ordered) + 1)
        right = [0] * (len(ordered) + 1)
        for i, cell in enumerate(ordered):
            left[i + 1] = left[i] | self.obligations[cell]
        for i in range(len(ordered) - 1, -1, -1):
            right[i] = right[i + 1] | self.obligations[ordered[i]]
        ranked: list[tuple[int, int, int, int]] = []
        for i, cell in enumerate(ordered):
            self.order_evaluations += 1
            if self.order_evaluations > self.limits.max_order_evaluations:
                raise FrontierCapacityError('Structural ordering evaluation limit')
            future = left[i] | right[i + 1]
            live_bits = ((processed | self.obligations[cell]) & future).bit_count()
            ranked.append((live_bits, -cell, cell, future))
        ranked.sort()
        return ranked

    def boundary_order(self, cells: tuple[int, ...]) -> tuple[int, ...]:
        """Greedy minimum next obligation boundary, stable largest-cell tie."""
        remaining = set(cells)
        selected: list[int] = []
        processed = 0
        while remaining:
            _, _, chosen, _ = self.rank_boundary_candidates(remaining, processed)[0]
            selected.append(chosen)
            remaining.remove(chosen)
            processed |= self.obligations[chosen]
        return tuple(selected)

    def reachable_count(self, cells: tuple[int, ...]) -> tuple[int, tuple[int, ...]]:
        """Exact contraction with sampled *reachable-state* ordering probes.

        Probes only choose the next cell. All prefix multiplicities are
        retained and exactly contracted using the shared forward step.
        The pilot's additional work is counted and has a hard refusal budget.
        """
        remaining = set(cells)
        selected: list[int] = []
        processed = 0
        table: dict[int, int] = {0: 1}
        self.work.guard(len(table))
        while remaining:
            ranked = self.rank_boundary_candidates(remaining, processed)
            step = max(1, len(table) // self.limits.pilot_sample_states)
            sample = tuple(islice(islice(table, 0, None, step),
                                  self.limits.pilot_sample_states))
            best: tuple[int, int, int] | None = None
            chosen = -1
            future = 0
            for width, tie, cell, mask in ranked[:self.limits.pilot_candidate_cells]:
                self.pilot_evaluations += 1
                signatures: set[int] = set()
                for signature in sample:
                    for candidate in self.options[cell]:
                        self.pilot_transitions += 1
                        if self.pilot_transitions > self.limits.max_pilot_transitions:
                            raise FrontierCapacityError('Reachability pilot transition limit')
                        if not (signature & candidate):
                            signatures.add((signature | candidate) & mask)
                # Exact integer comparison of states * 2**(width / 8),
                # raised to the eighth power to avoid floating-point ties.
                score = (len(signatures)**8 << width, width, tie)
                if best is None or score < best:
                    best = score
                    chosen = cell
                    future = mask
            table = _advance_forward(table, self.options[chosen], future, self.work)
            selected.append(chosen)
            remaining.remove(chosen)
            processed |= self.obligations[chosen]
            if not table:
                return 0, tuple(selected)
        return sum(table.values()), tuple(selected)

    def boundary_width(self, ordered: tuple[int, ...]) -> int:
        """Maximum prefix/suffix overlap before counting, in obligation bits."""
        suffix = [0] * (len(ordered) + 1)
        for pos in range(len(ordered) - 1, -1, -1):
            suffix[pos] = suffix[pos + 1] | self.obligations[ordered[pos]]
        prefix = width = 0
        for pos, cell in enumerate(ordered):
            prefix |= self.obligations[cell]
            width = max(width, (prefix & suffix[pos + 1]).bit_count())
        return width

    def separator_plan(self) -> tuple[_Plan | None, bool, int | None]:
        """Return best witnessed separator and whether the search was exhaustive.

        Exhaustive is relative to the declared number of separator cells, not
        a statement about the graph's unbounded vertex connectivity.
        """
        best: _Plan | None = None
        smallest: int | None = None
        complete = True
        for size in range(1, min(self.limits.max_separator_cells,
                                 len(self.cells) - 1) + 1):
            for selected in combinations(self.cells, size):
                if self.probes >= self.limits.max_separator_probes:
                    complete = False
                    return best, complete, smallest
                self.probes += 1
                assignments = prod(len(self.options[c]) for c in selected)
                groups = self.components(selected)
                if len(groups) < 2:
                    continue
                if smallest is None:
                    smallest = size
                if assignments > self.limits.max_separator_assignments:
                    continue
                # Explicitly a cheap heuristic, not a bound on runtime.
                proxy = assignments * sum(1 << min(len(g), 60) for g in groups)
                plan = _Plan(selected, groups, assignments, proxy)
                if best is None or (proxy, size, selected) < (
                    best.proxy_cost, len(best.separator), best.separator
                ):
                    best = plan
        return best, complete, smallest


def count_structural(
    puzzle: Puzzle, *, method: StructuralMethod = 'boundary',
    domains: Sequence[int] | None = None,
    limits: StructuralLimits = StructuralLimits(),
) -> StructuralResult:
    """Count exact Sudoku completions, optionally conditioning on a separator.

    ``domains`` restricts the counted problem and is not assumed to be a
    support-preserving transformation of the original puzzle. ``condition``
    requires an explicitly found graph separator; ``boundary`` (the
    default) only reorders the standard forward recurrence; ``auto``
    uses a separator only when a heuristic work proxy favors it.
    ``reachable`` samples
    current frontier states to select the next cell. All counts remain exact.
    """
    if method not in ('auto', 'boundary', 'condition', 'reachable'):
        raise ValueError('Unknown structural counting method')
    options, satisfiable = prepare_residual(puzzle, domains)
    if not satisfiable:
        return StructuralResult(0, StructuralStats(
            0, 0, 0, 0, 0, True, None, (), (), 0, 0, 0, 0, 0, 0, 0, 0,
            'contradiction'))
    work = _Work(puzzle.side, ComponentLimits(
        frontier=limits.frontier, max_graph_visits=limits.max_graph_visits))
    planner = _Planner(options, limits, work)
    initial = planner.components()
    plan: _Plan | None = None
    complete = len(initial) != 1
    minimum: int | None = None
    if len(initial) == 1 and method in ('auto', 'condition') and options:
        plan, complete, minimum = planner.separator_plan()
    if method == 'condition' and plan is None and len(initial) == 1:
        raise FrontierCapacityError('No eligible separator found within limits')
    if plan is not None and method == 'auto':
        whole_proxy = 1 << min(len(options), 60)
        if plan.proxy_cost >= whole_proxy:
            plan = None

    ordered: tuple[tuple[int, ...], ...]
    chosen: tuple[int, ...] = ()
    considered = compatible = 0
    if plan is None:
        count = 1
        performed: list[tuple[int, ...]] = []
        for group in initial:
            if method == 'reachable':
                group_count, group_order = planner.reachable_count(group)
            else:
                group_order = planner.boundary_order(group)
                group_count = _count_forward(group_order, options, work)
            performed.append(group_order)
            count *= group_count
            if count == 0:
                break
        ordered = tuple(performed)
        if len(initial) == 1:
            mode = 'reachable' if method == 'reachable' else 'boundary'
        else:
            mode = 'independent-components'
        comp_sizes = tuple(len(group) for group in initial)
    else:
        chosen = plan.separator
        ordered = tuple(planner.boundary_order(group) for group in plan.components)
        comp_sizes = tuple(len(group) for group in plan.components)
        count = 0
        # Before iteration, the entire cartesian-product bound was checked.
        for assignment in product(*(options[cell] for cell in chosen)):
            considered += 1
            occupied = 0
            for candidate in assignment:
                work.transition(not bool(occupied & candidate))
                if occupied & candidate:
                    break
                occupied |= candidate
            else:
                compatible += 1
                branch_count = 1
                for group in ordered:
                    filtered = {cell: tuple(candidate for candidate in options[cell]
                                            if not candidate & occupied)
                                for cell in group}
                    if any(not candidates for candidates in filtered.values()):
                        branch_count = 0
                        break
                    branch_count *= _count_forward(group, filtered, work)
                    if branch_count == 0:
                        break
                count += branch_count
        mode = 'condition'

    stats = StructuralStats(
        fixed_cells=len(puzzle.entries) - len(options),
        free_cells=len(options), conflict_edges=planner.edges,
        initial_components=len(initial), separator_probes=planner.probes,
        separator_search_complete=complete,
        smallest_separator_size=minimum,
        chosen_separator=chosen, resulting_component_sizes=comp_sizes,
        considered_separator_assignments=considered,
        compatible_separator_assignments=compatible,
        boundary_order_evaluations=planner.order_evaluations,
        boundary_width_upper_bound=max((planner.boundary_width(group)
                                        for group in ordered), default=0),
        peak_states=work.peak_states, transitions=work.transitions,
        compatible_transitions=work.compatible,
        graph_visits=work.graph_visits, method_used=mode,
        pilot_evaluations=planner.pilot_evaluations,
        pilot_transitions=planner.pilot_transitions)
    return StructuralResult(count, stats)
