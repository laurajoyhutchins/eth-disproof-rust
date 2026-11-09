"""Exact Sudoku frontier contraction with bounded dictionary/ZDD migration.

Both representations store the same finite function: occupied unit-digit
obligations -> nonnegative integer multiplicity. A conversion is exact, never
an approximation, and changes neither the candidate transition nor the count.

Conversion is *measured* before switching: a bounded projection-diversity
preflight screens likely-unhelpful conversions without constructing a trial
ZDD. A full conversion is retained only when its measured steady-state
storage is smaller by the configured factor. The conversion cost is always counted. An existing
ZDD may return to the dictionary only when the full support fits within the
stated state and byte budgets. No SAT oracle or search fallback is used.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import islice
from typing import Literal, Sequence

from .state import prepare_residual
from .frontier import FrontierCapacityError, FrontierLimits
from .three_cnf import Puzzle
from .weighted_zdd import (
    ZDDLimits, ZDDOrderLimits, _Budget, _Diagram, _choose_reachable_cell,
    _relabel_choices,
)

HybridOrder = Literal['row-major', 'minimum-domain', 'reachable']
HybridBits = Literal['digit-major', 'unit-major', 'digit-activity', 'digit-incidence']


@dataclass(frozen=True)
class HybridLimits:
    frontier: FrontierLimits = FrontierLimits()
    diagram: ZDDLimits = ZDDLimits()
    ordering: ZDDOrderLimits = ZDDOrderLimits()
    min_switch_states: int = 2048
    max_conversion_states: int = 10_000
    min_savings_percent: int = 30
    switch_cooldown: int = 4
    max_conversion_work: int = 8_000_000
    max_switch_attempts: int = 4
    sample_probe_states: int = 64
    max_sample_nodes_per_state: int = 12
    preflight: Literal['projected-blocks', 'sample-zdd'] = 'sample-zdd'
    max_block_variants: int = 12
    max_prediction_work: int = 100_000

    def __post_init__(self) -> None:
        if (self.min_switch_states < 1 or self.max_conversion_states < 1
                or not 0 <= self.min_savings_percent < 100
                or self.switch_cooldown < 0 or self.max_conversion_work < 1
                or self.max_switch_attempts < 0
                or self.sample_probe_states < 1
                or self.max_sample_nodes_per_state < 1
                or self.max_block_variants < 1 or self.max_prediction_work < 1
                or self.preflight not in ('projected-blocks', 'sample-zdd')):
            raise ValueError('Invalid hybrid limits')


@dataclass(frozen=True)
class HybridLayer:
    """Measured state counts and work after one exact contraction step."""

    step: int
    cell: int
    representation: Literal['dictionary', 'zdd']
    switch: Literal['none', 'to-zdd', 'to-dictionary']
    represented_states: int
    dictionary_states: int
    live_diagram_nodes: int
    estimated_retained_bytes: int
    cumulative_dictionary_transitions: int
    cumulative_diagram_operations: int
    cumulative_conversion_work: int
    sampled_max_block_variants: int | None = None


@dataclass(frozen=True)
class HybridStats:
    fixed_cells: int
    free_cells: int
    contracted_cells: int
    complete: bool
    peak_dictionary_states: int
    peak_diagram_nodes: int
    peak_represented_states: int
    dictionary_transitions: int
    diagram_operations: int
    pilot_transitions: int
    conversion_work: int
    conversion_attempts: int
    sample_rejections: int
    dictionary_to_diagram: int
    diagram_to_dictionary: int
    final_representation: str
    final_states: int
    final_nodes: int
    estimated_peak_bytes: int
    layers: tuple[HybridLayer, ...] = ()
    prediction_checks: int = 0
    prediction_work: int = 0
    prediction_rejections: int = 0


@dataclass(frozen=True)
class HybridResult:
    count: int
    stats: HybridStats


class _Conversions:
    def __init__(self, maximum_work: int) -> None:
        self.maximum = maximum_work
        self.work = 0

    def charge(self, quantity: int = 1) -> None:
        self.work += quantity
        if self.work > self.maximum:
            raise FrontierCapacityError('Hybrid conversion-work limit')


def _pack(
    table: dict[int, int], budget: _Budget, conversions: _Conversions,
    retained_estimated_bytes: int = 0,
) -> tuple[_Diagram, int]:
    """Canonical weighted ZDD directly from a finite map, with no SAT work."""
    if retained_estimated_bytes < 0:
        raise ValueError('Retained estimate must be nonnegative')
    retained_nodes = (retained_estimated_bytes + 191) // 192
    diagram = _Diagram(budget, old_nodes=retained_nodes)
    def build(items: list[tuple[int, int]]) -> int:
        conversions.charge(len(items))
        if not items:
            return 0
        if len(items) == 1 and items[0][0] == 0:
            weight = items[0][1]
            return -budget.coefficient(weight)
        mask = 0
        for signature, _ in items:
            mask |= signature
        if not mask:
            if len(items) != 1:
                raise AssertionError('Duplicate hybrid frontier signatures')
            return -budget.coefficient(items[0][1])
        bit = (mask & -mask).bit_length() - 1
        selector = 1 << bit
        without: list[tuple[int, int]] = []
        with_bit: list[tuple[int, int]] = []
        for signature, weight in items:
            if signature & selector:
                with_bit.append((signature ^ selector, weight))
            else:
                without.append((signature, weight))
        return diagram.make(bit, build(without), build(with_bit))

    try:
        root = build(list(sorted(table.items())))
    except RecursionError as exc:
        raise FrontierCapacityError('Hybrid pack recursion-depth limit') from exc
    return diagram, root


def _unpack(diagram: _Diagram, root: int, max_states: int,
            conversions: _Conversions) -> dict[int, int]:
    """Bounded expansion of exact weighted support, with no truncation."""
    result: dict[int, int] = {}
    def visit(node: int, signature: int) -> None:
        conversions.charge()
        if node == 0:
            return
        if node < 0:
            if len(result) >= max_states:
                raise FrontierCapacityError('Hybrid unpack state limit')
            if signature in result:
                raise AssertionError('Duplicate hybrid unpack signature')
            result[signature] = -node
            return
        bit, low, high = diagram.nodes[node]
        visit(low, signature)
        visit(high, signature | (1 << bit))
    try:
        visit(root, 0)
    except RecursionError as exc:
        raise FrontierCapacityError('Hybrid unpack recursion-depth limit') from exc
    return result


def _projected_block_diversity(
    sample: tuple[int, ...], side: int, max_work: int, used_work: int,
) -> tuple[int, int]:
    """Upper-tail statistic for sampled digit-sized blocks; not a ZDD estimate.

    Bit order is already the selected ZDD order. Grouping its contiguous
    3*side-bit blocks inspects the actual frontier support, but creates no
    decision-diagram nodes. The statistic is only a rejection heuristic;
    it makes no claim about the size of a weighted ZDD.
    """
    width = 3 * side
    mask = (1 << width) - 1
    most = 0
    for block in range(side):
        seen: set[int] = set()
        shift = block * width
        for signature in sample:
            used_work += 1
            if used_work > max_work:
                raise FrontierCapacityError('Hybrid prediction-work limit')
            seen.add((signature >> shift) & mask)
        most = max(most, len(seen))
    return most, used_work


def _choose_dictionary(
    table: dict[int, int], remaining: set[int],
    options: dict[int, tuple[int, ...]], obligations: dict[int, int],
    processed: int, limits: ZDDOrderLimits, evaluations: int,
    transitions: int,
) -> tuple[int, int, int, int]:
    ordered = sorted(remaining)
    left = [0] * (len(ordered) + 1)
    right = [0] * (len(ordered) + 1)
    for index, cell in enumerate(ordered):
        left[index + 1] = left[index] | obligations[cell]
    for index in range(len(ordered) - 1, -1, -1):
        right[index] = right[index + 1] | obligations[ordered[index]]
    ranked: list[tuple[int, int, int, int]] = []
    for index, cell in enumerate(ordered):
        evaluations += 1
        if evaluations > limits.max_order_evaluations:
            raise FrontierCapacityError('Hybrid ordering evaluation limit')
        keep = left[index] | right[index + 1]
        width = ((processed | obligations[cell]) & keep).bit_count()
        ranked.append((width, -cell, cell, keep))
    ranked.sort()
    stride = max(1, len(table) // limits.pilot_sample_states)
    sample = tuple(islice(islice(table, 0, None, stride), limits.pilot_sample_states))
    best: tuple[int, int, int] | None = None
    chosen = -1
    selected_keep = 0
    for width, tie, cell, keep in ranked[:limits.pilot_candidate_cells]:
        projected: set[int] = set()
        for signature in sample:
            for candidate in options[cell]:
                transitions += 1
                if transitions > limits.max_pilot_transitions:
                    raise FrontierCapacityError('Hybrid pilot transition limit')
                if not signature & candidate:
                    projected.add((signature | candidate) & keep)
        score = (len(projected)**8 << width, width, tie)
        if best is None or score < best:
            best, chosen, selected_keep = score, cell, keep
    return chosen, selected_keep, evaluations, transitions


def contract_hybrid(
    puzzle: Puzzle, *, limits: HybridLimits = HybridLimits(),
    order: HybridOrder = 'row-major',
    bit_order: HybridBits = 'digit-major',
    prefix_cells: int | None = None,
    domains: Sequence[int] | None = None,
    initial: Literal['dictionary', 'zdd'] = 'dictionary',
) -> HybridResult:
    """Count the exact complete Sudoku, or a declared prefix when requested.

    A prefix count is the number of compatible partial assignments, *not*
    the number of completed Sudoku grids. ``domains`` impose additional
    restrictions and change the counted problem.
    """
    if initial not in ('dictionary', 'zdd'):
        raise ValueError('Unknown hybrid initial representation')
    if order not in ('row-major', 'minimum-domain', 'reachable'):
        raise ValueError('Unknown hybrid cell order')
    if bit_order not in ('digit-major', 'unit-major', 'digit-activity', 'digit-incidence'):
        raise ValueError('Unknown hybrid bit order')
    options, valid = prepare_residual(puzzle, domains)
    options = _relabel_choices(options, puzzle.side, bit_order)
    ordered = sorted(options)
    if order == 'minimum-domain':
        ordered.sort(key=lambda cell: (len(options[cell]), cell))
    total = len(ordered)
    if prefix_cells is not None and (type(prefix_cells) is not int
                                     or not 0 <= prefix_cells <= total):
        raise ValueError('Invalid hybrid prefix length')
    count_cells = total if prefix_cells is None else prefix_cells
    complete = count_cells == total
    if not valid:
        return HybridResult(0, HybridStats(
            len(puzzle.entries), 0, 0, complete, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 'dictionary', 0, 0, 0))
    future = [0] * (total + 1)
    if order != 'reachable':
        for pos in range(total - 1, -1, -1):
            union = 0
            for choice in options[ordered[pos]]:
                union |= choice
            future[pos] = future[pos + 1] | union
    obligations = {cell: 0 for cell in ordered}
    if order == 'reachable':
        for cell, choices in options.items():
            for choice in choices:
                obligations[cell] |= choice
    remaining = set(ordered)
    consumed = 0
    estimated_dict_state = 160 + 2 * ((3 * puzzle.side * puzzle.side + 7) // 8)
    budget = _Budget(limits.diagram)
    conversions = _Conversions(limits.max_conversion_work)
    table: dict[int, int] | None = {0: 1} if initial == 'dictionary' else None
    diagram: _Diagram | None = _Diagram(budget) if initial == 'zdd' else None
    root = -1 if initial == 'zdd' else 0
    represented = 1
    live_nodes = 0
    peak_dict = 1
    peak_zdd = 0
    peak_states = 1
    peak_bytes = estimated_dict_state
    transitions = 0
    attempts = packed = unpacked = sample_rejections = 0
    prediction_checks = prediction_work = prediction_rejections = 0
    last_attempt = -limits.switch_cooldown - 1
    evaluations = pilot = 0
    count = 1
    layers: list[HybridLayer] = []

    def guard_dict(retained: int, building: int) -> None:
        if building > limits.frontier.max_states:
            raise FrontierCapacityError('Hybrid dictionary state limit')
        if (retained + building) * estimated_dict_state > limits.frontier.max_estimated_bytes:
            raise FrontierCapacityError('Hybrid dictionary estimated-byte limit')

    if table is not None:
        guard_dict(0, len(table))

    for pos in range(count_cells):
        if order == 'reachable':
            if table is not None:
                cell, keep, evaluations, pilot = _choose_dictionary(
                    table, remaining, options, obligations, consumed,
                    limits.ordering, evaluations, pilot)
            else:
                if diagram is None:
                    raise AssertionError('Missing hybrid representation')
                cell, keep, evaluations, pilot, _ = _choose_reachable_cell(
                    diagram, root, remaining, options, obligations, consumed,
                    limits.ordering, evaluations, pilot)
            remaining.remove(cell)
            consumed |= obligations[cell]
        else:
            cell, keep = ordered[pos], future[pos + 1]
        if table is not None:
            output: dict[int, int] = {}
            for signature, multiplicity in table.items():
                for choice in options[cell]:
                    transitions += 1
                    if transitions > limits.frontier.max_transitions:
                        raise FrontierCapacityError('Hybrid dictionary transition limit')
                    if signature & choice:
                        continue
                    key = (signature | choice) & keep
                    if key in output:
                        output[key] += multiplicity
                        if output[key].bit_length() > limits.diagram.max_coefficient_bits:
                            raise FrontierCapacityError('Hybrid coefficient-bit limit')
                    else:
                        guard_dict(len(table), len(output) + 1)
                        if multiplicity.bit_length() > limits.diagram.max_coefficient_bits:
                            raise FrontierCapacityError('Hybrid coefficient-bit limit')
                        output[key] = multiplicity
            peak_bytes = max(peak_bytes, (len(table) + len(output)) * estimated_dict_state)
            table = output
            peak_dict = max(peak_dict, len(table))
            count = sum(table.values())
            represented = len(table)
        else:
            if diagram is None:
                raise AssertionError('Missing diagram')
            try:
                fresh = _Diagram(budget, diagram.size)
                combined = 0
                for choice in options[cell]:
                    combined = fresh.add(combined,
                                         fresh.transition(diagram, root, choice, keep))
                count, represented, live_nodes = fresh.totals(combined)
                root = fresh.compact(combined)
                diagram = fresh
            except RecursionError as exc:
                raise FrontierCapacityError('Hybrid diagram recursion-depth limit') from exc
            peak_zdd = max(peak_zdd, live_nodes)
            peak_bytes = max(peak_bytes, budget.peak_allocated * 192)
        peak_states = max(peak_states, represented)
        switch: Literal['none', 'to-zdd', 'to-dictionary'] = 'none'
        sampled_max_block_variants: int | None = None
        if (count and attempts < limits.max_switch_attempts
                and pos - last_attempt > limits.switch_cooldown):
            if table is not None:
                if limits.min_switch_states <= len(table) <= limits.max_conversion_states:
                    attempts += 1
                    last_attempt = pos
                    # A sample is used only to decide whether to attempt an
                    # exact conversion. A rejected prediction never changes
                    # the weighted frontier or its exact solution count.
                    stride = max(1, len(table) // limits.sample_probe_states)
                    sample = dict(islice(islice(table.items(), 0, None, stride),
                                         limits.sample_probe_states))
                    rejected = False
                    if limits.preflight == 'projected-blocks':
                        prediction_checks += 1
                        sampled_max_block_variants, prediction_work = (
                            _projected_block_diversity(
                                tuple(sample), puzzle.side,
                                limits.max_prediction_work, prediction_work))
                        rejected = (sampled_max_block_variants
                                    > limits.max_block_variants)
                        if rejected:
                            prediction_rejections += 1
                    else:
                        # Historical v0.38 trial-ZDD sample for controlled A/B.
                        small, small_root = _pack(
                            sample, budget, conversions,
                            retained_estimated_bytes=len(table) * estimated_dict_state)
                        _, _, small_nodes = small.totals(small_root)
                        peak_bytes = max(peak_bytes, len(table) * estimated_dict_state
                                         + small.size * 192)
                        rejected = (small_nodes >
                                    limits.max_sample_nodes_per_state * len(sample))
                    if rejected:
                        sample_rejections += 1
                    else:
                        candidate, candidate_root = _pack(
                            table, budget, conversions,
                            retained_estimated_bytes=len(table) * estimated_dict_state)
                        verified_mass, verified_states, candidate_nodes = candidate.totals(
                            candidate_root)
                        if verified_states != len(table) or verified_mass != count:
                            raise AssertionError('Hybrid packing changed weighted support')
                        peak_bytes = max(peak_bytes, estimated_dict_state * len(table)
                                         + candidate.size * 192)
                        if (candidate_nodes * 192 * 100 <=
                                len(table) * estimated_dict_state
                                * (100 - limits.min_savings_percent)):
                            root = candidate.compact(candidate_root)
                            diagram = candidate
                            live_nodes = candidate_nodes
                            peak_zdd = max(peak_zdd, live_nodes)
                            table = None
                            packed += 1
                            switch = 'to-zdd'
            elif (diagram is not None and represented <= limits.max_conversion_states
                  and represented <= limits.frontier.max_states
                  and represented * estimated_dict_state <= limits.frontier.max_estimated_bytes
                  and (represented * estimated_dict_state + live_nodes * 192
                       <= min(limits.frontier.max_estimated_bytes,
                              limits.diagram.max_estimated_bytes))
                  and represented * estimated_dict_state * 100 <=
                  live_nodes * 192 * (100 - limits.min_savings_percent)):
                attempts += 1
                last_attempt = pos
                unpacked_table = _unpack(diagram, root, limits.max_conversion_states,
                                          conversions)
                if (len(unpacked_table) != represented
                        or sum(unpacked_table.values()) != count):
                    raise AssertionError('Hybrid unpack changed the exact count')
                peak_bytes = max(peak_bytes, live_nodes * 192
                                 + len(unpacked_table) * estimated_dict_state)
                table = unpacked_table
                diagram = None
                live_nodes = 0
                unpacked += 1
                switch = 'to-dictionary'
        mode: Literal['dictionary', 'zdd'] = 'dictionary' if table is not None else 'zdd'
        layers.append(HybridLayer(
            pos + 1, cell, mode, switch, represented,
            len(table) if table is not None else 0, live_nodes,
            len(table) * estimated_dict_state if table is not None else live_nodes * 192,
            transitions, budget.operations, conversions.work,
            sampled_max_block_variants))
        if count == 0:
            break
    return HybridResult(count, HybridStats(
        len(puzzle.entries) - total, total, len(layers),
        complete, peak_dict, peak_zdd, peak_states, transitions,
        budget.operations, pilot, conversions.work, attempts,
        sample_rejections, packed, unpacked, 'dictionary' if table is not None else 'zdd',
        represented, live_nodes, peak_bytes, tuple(layers),
        prediction_checks, prediction_work, prediction_rejections))
