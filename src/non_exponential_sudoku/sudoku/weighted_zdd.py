"""Exact weighted zero-suppressed diagrams for Sudoku frontier contraction.

A weighted ZDD represents a finite function from sets of occupied unit-digit
obligations to nonnegative integer multiplicities.  The zero terminal is the
zero function; a negative node identifier ``-m`` holds multiplicity ``m`` on
the empty set.  An internal node ``(bit, low, high)`` separates sets which do
not/do contain that bit.  A zero high branch is omitted (zero suppression).

Each Sudoku choice is implemented algebraically: restrict its three occupied
bits to zero, adjoin the chosen bits, project out obligations that no future
cell can inspect, and add the resulting weighted families.  The full state
mapping is never expanded.  Counts and compression are exact; nodes and
algebraic operations are bounded.  This is not a polynomial-time solver.

A restricted ``prefix_cells`` call returns a *partial-assignment* count,
not a full Sudoku completion count.  Fixed cells are removed by the same
validated preprocessing used by the dictionary frontier.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Sequence

from .state import prepare_residual
from .frontier import FrontierCapacityError
from .three_cnf import Puzzle


@dataclass(frozen=True)
class ZDDLimits:
    max_nodes: int = 100_000
    max_operations: int = 5_000_000
    max_estimated_bytes: int = 128 * 1024 * 1024
    max_coefficient_bits: int = 1_000_000

    def __post_init__(self) -> None:
        if min(self.max_nodes, self.max_operations, self.max_estimated_bytes,
               self.max_coefficient_bits) < 1:
            raise ValueError('ZDD limits must be positive')


@dataclass(frozen=True)
class ZDDOrderLimits:
    """Finite work limits for ZDD-native reachability ordering.

    Sampling examines representative support signatures, not the complete
    dictionary of reachable signatures.  The chosen order is heuristic; all
    counting transitions are exact.
    """

    max_pilot_transitions: int = 1_000_000
    max_order_evaluations: int = 100_000
    pilot_sample_states: int = 64
    pilot_candidate_cells: int = 12

    def __post_init__(self) -> None:
        if (self.max_pilot_transitions < 1 or self.max_order_evaluations < 1
                or not 1 <= self.pilot_sample_states <= 4096
                or not 1 <= self.pilot_candidate_cells <= 256):
            raise ValueError('Invalid ZDD ordering limits')


@dataclass(frozen=True)
class ZDDStats:
    fixed_cells: int
    free_cells: int
    contracted_cells: int
    complete: bool
    peak_nodes: int
    peak_allocated_nodes: int
    peak_represented_states: int
    algebraic_operations: int
    final_nodes: int
    final_represented_states: int
    pilot_evaluations: int = 0
    pilot_transitions: int = 0
    pilot_samples: int = 0


@dataclass(frozen=True)
class ZDDResult:
    count: int
    stats: ZDDStats


class _Budget:
    def __init__(self, limits: ZDDLimits) -> None:
        self.limits = limits
        self.operations = 0
        self.peak_allocated = 0

    def work(self) -> None:
        self.operations += 1
        if self.operations > self.limits.max_operations:
            raise FrontierCapacityError('ZDD algebraic-operation limit')

    def allocate(self, old_nodes: int, fresh_nodes: int) -> None:
        self.peak_allocated = max(self.peak_allocated, old_nodes + fresh_nodes)
        if fresh_nodes > self.limits.max_nodes:
            raise FrontierCapacityError('ZDD allocated-node limit')
        # Includes two simultaneously retained node tables, but is only a
        # conservative accounting model, not a resident-memory guarantee.
        if (old_nodes + fresh_nodes) * 192 > self.limits.max_estimated_bytes:
            raise FrontierCapacityError('ZDD estimated-byte limit')

    def coefficient(self, count: int) -> int:
        if count.bit_length() > self.limits.max_coefficient_bits:
            raise FrontierCapacityError('ZDD coefficient-bit limit')
        return count


class _Diagram:
    """One canonical layer. Nodes have positive IDs, terminals nonpositive."""

    def __init__(self, budget: _Budget, old_nodes: int = 0) -> None:
        self.budget = budget
        self.old_nodes = old_nodes
        self.nodes: list[tuple[int, int, int]] = [(0, 0, 0)]
        self.unique: dict[tuple[int, int, int], int] = {}
        self._addition: dict[tuple[int, int], int] = {}
        self._forced: dict[tuple[int, int], int] = {}

    @property
    def size(self) -> int:
        return len(self.nodes) - 1

    def make(self, bit: int, low: int, high: int) -> int:
        if high == 0:
            return low
        key = (bit, low, high)
        existing = self.unique.get(key)
        if existing is not None:
            return existing
        self.budget.allocate(self.old_nodes, self.size + 1)
        result = len(self.nodes)
        self.nodes.append(key)
        self.unique[key] = result
        return result

    def add(self, a: int, b: int) -> int:
        self.budget.work()
        if a == 0:
            return b
        if b == 0:
            return a
        if a < 0 and b < 0:
            return -self.budget.coefficient(-a - b)
        pair = (a, b) if a <= b else (b, a)
        cached = self._addition.get(pair)
        if cached is not None:
            return cached
        bit_a = self.nodes[a][0] if a > 0 else 1 << 30
        bit_b = self.nodes[b][0] if b > 0 else 1 << 30
        bit = min(bit_a, bit_b)
        lo_a, hi_a = ((self.nodes[a][1], self.nodes[a][2])
                       if bit_a == bit else (a, 0))
        lo_b, hi_b = ((self.nodes[b][1], self.nodes[b][2])
                       if bit_b == bit else (b, 0))
        value = self.make(bit, self.add(lo_a, lo_b), self.add(hi_a, hi_b))
        self._addition[pair] = value
        return value

    def force(self, root: int, bit: int) -> int:
        """Adjoin bit to every set, when all input sets omit that bit."""
        self.budget.work()
        if root == 0:
            return 0
        key = (root, bit)
        cached = self._forced.get(key)
        if cached is not None:
            return cached
        if root < 0 or self.nodes[root][0] > bit:
            result = self.make(bit, 0, root)
        else:
            current, low, high = self.nodes[root]
            if current == bit:
                raise AssertionError('Attempt to force a non-absent obligation')
            result = self.make(current, self.force(low, bit),
                               self.force(high, bit))
        self._forced[key] = result
        return result

    def transition(self, previous: _Diagram, root: int, candidate: int,
                   keep: int) -> int:
        """Reject conflicts, forget dead bits, then set surviving new bits."""
        memo: dict[int, int] = {}

        def project(node: int) -> int:
            self.budget.work()
            if node <= 0:
                return node
            cached = memo.get(node)
            if cached is not None:
                return cached
            bit, low, high = previous.nodes[node]
            mask = 1 << bit
            if mask & candidate:
                result = project(low)
            elif not mask & keep:
                result = self.add(project(low), project(high))
            else:
                result = self.make(bit, project(low), project(high))
            memo[node] = result
            return result

        selected = project(root)
        remaining = candidate & keep
        # Force in descending order to minimize intermediate diagram rebuilding.
        while remaining:
            bit = remaining.bit_length() - 1
            remaining ^= 1 << bit
            selected = self.force(selected, bit)
        return selected

    def compact(self, root: int) -> int:
        """Discard temporary nodes and caches before the next contraction."""
        live_nodes: list[tuple[int, int, int]] = [(0, 0, 0)]
        renumber: dict[int, int] = {}

        def retain(node: int) -> int:
            if node <= 0:
                return node
            existing = renumber.get(node)
            if existing is not None:
                return existing
            bit, low, high = self.nodes[node]
            new_low, new_high = retain(low), retain(high)
            mapped = len(live_nodes)
            live_nodes.append((bit, new_low, new_high))
            renumber[node] = mapped
            return mapped

        result = retain(root)
        self.nodes = live_nodes
        self.unique = {node: index for index, node in enumerate(live_nodes)
                       if index > 0}
        self._addition.clear()
        self._forced.clear()
        self.old_nodes = 0
        return result

    def sample_support(self, root: int, requested: int) -> tuple[int, ...]:
        """Sample evenly spaced *distinct signatures* without expanding them.

        The ZDD is ordered and zero-suppressed, so each root-to-terminal path
        identifies exactly one support signature.  Subtree cardinalities allow
        deterministic selection by rank, with work proportional to diagram
        size plus samples times depth, rather than support cardinality.
        Multiplicities do not affect the rank, only support membership.
        """
        counts: dict[int, int] = {0: 0}

        def support_size(node: int) -> int:
            self.budget.work()
            if node < 0:
                return 1
            if node in counts:
                return counts[node]
            _, low, high = self.nodes[node]
            result = support_size(low) + support_size(high)
            counts[node] = result
            return result

        total = support_size(root)
        if not total:
            return ()
        samples = min(requested, total)
        # Quantiles include both ends and never duplicate an integer rank.
        ranks = ([0] if samples == 1 else
                 [index * (total - 1) // (samples - 1)
                  for index in range(samples)])
        result: list[int] = []
        for rank in ranks:
            node = root
            signature = 0
            while node > 0:
                self.budget.work()
                bit, low, high = self.nodes[node]
                left_size = counts[low] if low >= 0 else 1
                if rank < left_size:
                    node = low
                else:
                    rank -= left_size
                    signature |= 1 << bit
                    node = high
            if node == 0 or rank != 0:
                raise AssertionError('Invalid diagram support rank')
            result.append(signature)
        return tuple(result)

    def totals(self, root: int) -> tuple[int, int, int]:
        """Return exact mass, nonzero signatures and reachable live nodes."""
        memo: dict[int, tuple[int, int]] = {}
        seen: set[int] = set()

        def visit(node: int) -> tuple[int, int]:
            if node == 0:
                return (0, 0)
            if node < 0:
                return (-node, 1)
            cached = memo.get(node)
            if cached is not None:
                return cached
            seen.add(node)
            _, low, high = self.nodes[node]
            a_mass, a_states = visit(low)
            b_mass, b_states = visit(high)
            value = a_mass + b_mass, a_states + b_states
            memo[node] = value
            return value

        mass, states = visit(root)
        return mass, states, len(seen)


def _relabel_choices(
    options: dict[int, tuple[int, ...]], side: int,
    bit_order: Literal['digit-major', 'unit-major', 'digit-activity', 'digit-incidence'],
) -> dict[int, tuple[int, ...]]:
    """Apply a bijection to the finite set of (unit, digit) obligations.

    Digit activity is the number of currently permitted cell choices using
    an obligation.  It groups by digit as before, but puts more frequently
    appearing obligations first within each digit.  This is a structural
    ordering heuristic, not a quotient or a linear-rank reduction.
    """
    if bit_order == 'unit-major':
        return options
    total_bits = 3 * side * side
    frequency = [0] * total_bits
    if bit_order in ('digit-activity', 'digit-incidence'):
        for choices in options.values():
            for choice in choices:
                bits = choice
                while bits:
                    bit = bits & -bits
                    bits ^= bit
                    frequency[bit.bit_length() - 1] += 1
    if bit_order == 'digit-incidence':
        # For each digit, each candidate touches one row-, column- and
        # box-obligation. Greedily cluster these co-occurring obligations.
        # This keeps all digit groups intact while changing their internal
        # ZDD variable order; only positions are permuted, never constraints.
        adjacent: list[dict[int, int]] = [{} for _ in range(total_bits)]
        for choices in options.values():
            for choice in choices:
                members: list[int] = []
                while choice:
                    bit = choice & -choice
                    choice ^= bit
                    members.append(bit.bit_length() - 1)
                for i, first in enumerate(members):
                    for second in members[i + 1:]:
                        adjacent[first][second] = adjacent[first].get(second, 0) + 1
                        adjacent[second][first] = adjacent[second].get(first, 0) + 1
        permutation: list[int] = []
        for digit in range(side):
            remaining = {unit * side + digit for unit in range(3 * side)}
            affinity: dict[int, int] = {bit: 0 for bit in remaining}
            while remaining:
                chosen = min(remaining, key=lambda bit: (
                    -affinity[bit], -frequency[bit], bit // side,
                ))
                permutation.append(chosen)
                remaining.remove(chosen)
                for neighbor, weight in adjacent[chosen].items():
                    if neighbor in remaining:
                        affinity[neighbor] += weight
    else:
        permutation = sorted(range(total_bits), key=lambda original: (
            original % side,
            -frequency[original] if bit_order == 'digit-activity' else 0,
            original // side,
        ))
    new_position = {bit: rank for rank, bit in enumerate(permutation)}
    translated: dict[int, tuple[int, ...]] = {}
    for cell, choices in options.items():
        new_choices: list[int] = []
        for choice in choices:
            mask = 0
            while choice:
                bit = choice & -choice
                choice ^= bit
                mask |= 1 << new_position[bit.bit_length() - 1]
            new_choices.append(mask)
        translated[cell] = tuple(new_choices)
    return translated


def _choose_reachable_cell(
    old: _Diagram, root: int, remaining: set[int],
    options: dict[int, tuple[int, ...]], obligations: dict[int, int],
    processed: int, limits: ZDDOrderLimits,
    pilot_evaluations: int, pilot_transitions: int,
) -> tuple[int, int, int, int, int]:
    """Select a next cell from sampled ZDD support; return audited work.

    Width is used to shortlist cells, and sampled projected signatures
    estimate actual reachable-state growth.  Every actual contraction is
    still the exact ZDD recurrence and the heuristic cannot alter a count.
    """
    ordered = sorted(remaining)
    left = [0] * (len(ordered) + 1)
    right = [0] * (len(ordered) + 1)
    for index, cell in enumerate(ordered):
        left[index + 1] = left[index] | obligations[cell]
    for index in range(len(ordered) - 1, -1, -1):
        right[index] = right[index + 1] | obligations[ordered[index]]
    ranked: list[tuple[int, int, int, int]] = []
    for index, cell in enumerate(ordered):
        pilot_evaluations += 1
        if pilot_evaluations > limits.max_order_evaluations:
            raise FrontierCapacityError('ZDD ordering evaluation limit')
        future = left[index] | right[index + 1]
        width = ((processed | obligations[cell]) & future).bit_count()
        ranked.append((width, -cell, cell, future))
    ranked.sort()
    sample = old.sample_support(root, limits.pilot_sample_states)
    best: tuple[int, int, int] | None = None
    selected = -1
    selected_future = 0
    for width, tie, cell, future in ranked[:limits.pilot_candidate_cells]:
        projected: set[int] = set()
        for signature in sample:
            for candidate in options[cell]:
                pilot_transitions += 1
                if pilot_transitions > limits.max_pilot_transitions:
                    raise FrontierCapacityError('ZDD ordering pilot transition limit')
                if not signature & candidate:
                    projected.add((signature | candidate) & future)
        score = (len(projected)**8 << width, width, tie)
        if best is None or score < best:
            best = score
            selected = cell
            selected_future = future
    return selected, selected_future, pilot_evaluations, pilot_transitions, len(sample)


def contract_zdd(
    puzzle: Puzzle, *, limits: ZDDLimits = ZDDLimits(),
    order: Literal['row-major', 'minimum-domain', 'reachable'] = 'row-major',
    bit_order: Literal['digit-major', 'unit-major', 'digit-activity', 'digit-incidence'] = 'digit-major',
    prefix_cells: int | None = None,
    domains: Sequence[int] | None = None,
    ordering_limits: ZDDOrderLimits = ZDDOrderLimits(),
) -> ZDDResult:
    """Count complete or explicitly requested prefix-consistent assignments.

    ``reachable`` samples quantiles of the *compressed diagram support* to
    select the next cell, without expanding the frontier dictionary.  The
    separately bounded pilot is heuristic; the actual sum/product operations
    stay exact.  Prefix counts refer to the chosen order, and are not counts
    of full-grid completions unless ``complete`` is true.

    Restrictions in ``domains`` change the counted problem; they are not
    assumed to preserve the unrestricted Sudoku solution set.
    """
    if order not in ('row-major', 'minimum-domain', 'reachable'):
        raise ValueError('Unknown ZDD cell ordering')
    if bit_order not in ('digit-major', 'unit-major', 'digit-activity', 'digit-incidence'):
        raise ValueError('Unknown ZDD variable ordering')
    options, valid = prepare_residual(puzzle, domains)
    options = _relabel_choices(options, puzzle.side, bit_order)
    ordered = sorted(options)
    if order == 'minimum-domain':
        ordered.sort(key=lambda cell: (len(options[cell]), cell))
    total_cells = len(ordered)
    if prefix_cells is not None:
        if type(prefix_cells) is not int or not 0 <= prefix_cells <= total_cells:
            raise ValueError('Invalid ZDD prefix length')
    processed = total_cells if prefix_cells is None else prefix_cells
    complete = processed == total_cells
    if not valid:
        return ZDDResult(0, ZDDStats(
            len(puzzle.entries), 0, 0, complete, 0, 0, 0, 0, 0, 0))

    future = [0] * (total_cells + 1)
    if order != 'reachable':
        for pos in range(total_cells - 1, -1, -1):
            mask = future[pos + 1]
            for candidate in options[ordered[pos]]:
                mask |= candidate
            future[pos] = mask
    obligations = {cell: 0 for cell in options}
    if order == 'reachable':
        for cell, choices in options.items():
            for candidate in choices:
                obligations[cell] |= candidate
    remaining = set(ordered)
    occupied = 0
    pilot_evaluations = pilot_transitions = pilot_samples = 0
    budget = _Budget(limits)
    old = _Diagram(budget)
    root = -1
    peak_nodes = 0
    peak_states = 1
    final_nodes = 0
    final_states = 1
    count = 1
    for pos in range(processed):
        try:
            if order == 'reachable':
                (cell, keep, pilot_evaluations, pilot_transitions,
                 sampled) = _choose_reachable_cell(
                     old, root, remaining, options, obligations, occupied,
                     ordering_limits, pilot_evaluations, pilot_transitions)
                pilot_samples += sampled
                occupied |= obligations[cell]
                remaining.remove(cell)
            else:
                cell = ordered[pos]
                keep = future[pos + 1]
            new = _Diagram(budget, old.size)
            combined = 0
            for candidate in options[cell]:
                part = new.transition(old, root, candidate, keep)
                combined = new.add(combined, part)
            count, final_states, final_nodes = new.totals(combined)
            old, root = new, new.compact(combined)
        except RecursionError as exc:
            raise FrontierCapacityError('ZDD Python recursion-depth limit') from exc
        peak_nodes = max(peak_nodes, final_nodes)
        peak_states = max(peak_states, final_states)
        if count == 0:
            break
    return ZDDResult(count, ZDDStats(
        len(puzzle.entries) - total_cells, total_cells, processed, complete,
        peak_nodes, budget.peak_allocated, peak_states, budget.operations,
        final_nodes, final_states, pilot_evaluations, pilot_transitions,
        pilot_samples))
