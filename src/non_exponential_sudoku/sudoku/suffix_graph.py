"""Certified automorphism memoization for the *remaining* Sudoku exact-cover graph.

This is a separate exact counting path from the forward frontier contractor.
A symmetry of all remaining cells preserves its continuation count, but may
exchange the *next* cell with another cell. Consequently it is NOT safe to
merge forward orbit masses using just a representative transition. Instead,
cache the recursive continuation function on orbits of the suffix hypergraph.

Generators are concrete permutations of live unit/digit obligations, checked
against the candidate hypergraph. The optional NetworkX backend discovers
additional permutations of the unlabelled exact-cover incidence graph.
Every graph search, orbit and counting cache is explicitly bounded.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Literal, Sequence

from .frontier import FrontierCapacityError, FrontierLimits
from .state import initial_domains, candidate_bits
from .three_cnf import Puzzle

GraphMode = Literal['none', 'geometry', 'incidence']


@dataclass(frozen=True)
class SuffixGraphLimits:
    frontier: FrontierLimits = FrontierLimits()
    max_orbit: int = 4096
    max_generators: int = 24
    max_graph_choices: int = 24
    max_graph_isomorphisms: int = 240
    max_orbit_cache_entries: int = 100_000
    max_recursive_cells: int = 512

    def __post_init__(self) -> None:
        if min(self.max_orbit, self.max_generators, self.max_graph_choices,
               self.max_graph_isomorphisms, self.max_orbit_cache_entries,
               self.max_recursive_cells) < 1:
            raise ValueError('Suffix graph limits must be positive')


@dataclass(frozen=True)
class SuffixGraphStats:
    fixed_cells: int
    free_cells: int
    memo_states: int
    memo_hits: int
    transitions: int
    compatible_transitions: int
    peak_states_at_depth: int
    canonical_queries: int
    nontrivial_canonicalizations: int
    orbit_elements_examined: int
    layers_with_generators: int
    max_generators_at_layer: int
    graph_isomorphisms_examined: int
    orbit_cache_entries: int


@dataclass(frozen=True)
class SuffixGraphResult:
    count: int
    stats: SuffixGraphStats




def _cell_permutation_generators(side: int, block: int) -> tuple[tuple[int, ...], ...]:
    """Standard row/column/box geometry generators, including transpose.

    An arbitrary element need not be a symmetry of the remaining instance.
    Each proposed map is independently checked before being used.
    """
    result: list[tuple[int, ...]] = []
    def emit(rows: Sequence[int], cols: Sequence[int], transpose: bool = False) -> None:
        result.append(tuple((cols[c] * side + rows[r]) if transpose
                            else (rows[r] * side + cols[c])
                            for r in range(side) for c in range(side)))

    identity = list(range(side))
    for band in range(block):
        for i, j in combinations(range(band * block, (band + 1) * block), 2):
            rows = identity.copy()
            rows[i], rows[j] = rows[j], rows[i]
            emit(rows, identity)
    for stack in range(block):
        for i, j in combinations(range(stack * block, (stack + 1) * block), 2):
            cols = identity.copy()
            cols[i], cols[j] = cols[j], cols[i]
            emit(identity, cols)
    for left, right in combinations(range(block), 2):
        rows = identity.copy()
        for k in range(block):
            rows[left * block + k], rows[right * block + k] = (
                rows[right * block + k], rows[left * block + k])
        emit(rows, identity)
        cols = rows.copy()
        emit(identity, cols)
    emit(identity, identity, transpose=True)
    return tuple(result)


def _unit_map_from_cell_map(cell_map: Sequence[int], puzzle: Puzzle) -> tuple[int, ...]:
    """Find the unique image of each standard Sudoku unit, or reject."""
    units = tuple(frozenset(group) for group in puzzle.units())
    lookup = {cells: unit for unit, cells in enumerate(units)}
    try:
        mapped = tuple(lookup[frozenset(cell_map[cell] for cell in group)]
                       for group in units)
    except KeyError as err:
        raise ValueError('Proposed map does not preserve Sudoku units') from err
    if len(set(mapped)) != len(units):
        raise ValueError('Proposed map does not permute Sudoku units')
    return mapped


def _bit_permutation(unit_map: Sequence[int], side: int) -> tuple[int, ...]:
    return tuple(unit_map[bit // side] * side + bit % side
                 for bit in range(3 * side * side))


def _geometric_generators(
    puzzle: Puzzle, suffix_cells: Sequence[int], domains: Sequence[int],
) -> tuple[tuple[int, ...], ...]:
    if puzzle.b == 1:
        return ()
    remaining = set(suffix_cells)
    result: list[tuple[int, ...]] = []
    for cell_map in _cell_permutation_generators(puzzle.side, puzzle.b):
        if any(cell_map[cell] not in remaining
               or domains[cell] != domains[cell_map[cell]]
               for cell in suffix_cells):
            continue
        unit_map = _unit_map_from_cell_map(cell_map, puzzle)
        result.append(_bit_permutation(unit_map, puzzle.side))
    return tuple(dict.fromkeys(result))


def _certify_suffix_action(
    suffix_cells: Sequence[int], options: dict[int, tuple[int, ...]],
    cell_image: dict[int, int], permutation: Sequence[int],
) -> None:
    """Independently check that a proposed witness is a graph automorphism."""
    remaining = set(suffix_cells)
    if set(cell_image) != remaining or set(cell_image.values()) != remaining:
        raise ValueError('Automorphism does not permute the remaining cells')
    active = 0
    for cell in suffix_cells:
        for choice in options[cell]:
            active |= choice
    source_bits = {index for index in range(active.bit_length())
                   if active & (1 << index)}
    if {permutation[i] for i in source_bits} != source_bits:
        raise ValueError('Automorphism does not permute remaining obligations')
    for cell in suffix_cells:
        transformed = sorted(_transform(choice, permutation) for choice in options[cell])
        if transformed != sorted(options[cell_image[cell]]):
            raise ValueError('Automorphism does not preserve candidate hyperedges')


def _incidence_generators(
    suffix_cells: Sequence[int], options: dict[int, tuple[int, ...]],
    bit_count: int, limit: SuffixGraphLimits,
) -> tuple[tuple[tuple[int, ...], ...], int]:
    """Discover *actual* graph automorphisms, never infer them from colors.

    One vertex per remaining cell, candidate and unit-digit obligation. Each
    candidate vertex is joined to its cell and three obligations. A colored
    automorphism therefore preserves the exact-cover counting problem.
    """
    option_count = sum(len(options[cell]) for cell in suffix_cells)
    if option_count > limit.max_graph_choices:
        return (), 0
    try:
        import networkx as nx  # type: ignore[import-untyped]
    except ImportError as exc:
        raise ImportError(
            "Install the optional 'symmetry-graph' extra for incidence mode"
        ) from exc

    # Integer node IDs make NetworkX's internal node-set iteration stable
    # across PYTHONHASHSEED values. Capped automorphism enumeration must be
    # deterministic to produce reproducible subgroups and statistics.
    graph = nx.Graph()
    active_bits: set[int] = set()
    for cell in suffix_cells:
        for signature in options[cell]:
            bits = signature
            while bits:
                bit = bits & -bits
                bits ^= bit
                active_bits.add(bit.bit_length() - 1)
    cell_nodes = {cell: index for index, cell in enumerate(suffix_cells)}
    choice_nodes: dict[tuple[int, int], int] = {}
    next_node = len(cell_nodes)
    for cell in suffix_cells:
        for index in range(len(options[cell])):
            choice_nodes[cell, index] = next_node
            next_node += 1
    bit_nodes = {bit: next_node + index
                 for index, bit in enumerate(sorted(active_bits))}
    reverse_cell = {node: cell for cell, node in cell_nodes.items()}
    reverse_bit = {node: bit for bit, node in bit_nodes.items()}
    for cell in suffix_cells:
        graph.add_node(cell_nodes[cell], kind='cell')
        for index, signature in enumerate(options[cell]):
            choice = choice_nodes[cell, index]
            graph.add_node(choice, kind='choice')
            graph.add_edge(cell_nodes[cell], choice)
            bits = signature
            while bits:
                bit = bits & -bits
                bits ^= bit
                bit_index = bit.bit_length() - 1
                node = bit_nodes[bit_index]
                graph.add_node(node, kind='obligation')
                graph.add_edge(choice, node)
    matcher = nx.algorithms.isomorphism.GraphMatcher(
        graph, graph,
        node_match=lambda a, b: a['kind'] == b['kind'],
    )
    result: list[tuple[int, ...]] = []
    seen: set[tuple[int, ...]] = set()
    examined = 0
    for mapping in matcher.isomorphisms_iter():
        examined += 1
        bit_perm = list(range(bit_count))
        for bit in active_bits:
            target = mapping[bit_nodes[bit]]
            bit_perm[bit] = reverse_bit[target]
        perm = tuple(bit_perm)
        _certify_suffix_action(
            suffix_cells, options,
            {cell: reverse_cell[mapping[cell_nodes[cell]]]
             for cell in suffix_cells}, perm,
        )
        if perm != tuple(range(bit_count)) and perm not in seen:
            seen.add(perm)
            result.append(perm)
            if len(result) >= limit.max_generators:
                break
        if examined >= limit.max_graph_isomorphisms:
            break
    return tuple(result), examined


def _transform(signature: int, permutation: Sequence[int]) -> int:
    result = 0
    while signature:
        bit = signature & -signature
        signature ^= bit
        result |= 1 << permutation[bit.bit_length() - 1]
    return result


def count_suffix_graph(
    puzzle: Puzzle, *, mode: GraphMode = 'geometry',
    limits: SuffixGraphLimits = SuffixGraphLimits(),
    domains: Sequence[int] | None = None,
) -> SuffixGraphResult:
    """Count exact Sudoku completions, memoized modulo suffix automorphisms.

    This is recursive exact-cover dynamic programming, not polynomial time and
    not the forward-only tensor contractor. A graph automorphism may reorder
    the unprocessed cells, because only the *full continuation value* is
    quotiented, not the one-step transition distribution.
    """
    if mode not in ('none', 'geometry', 'incidence'):
        raise ValueError('Unknown suffix graph mode')
    n = puzzle.side
    if puzzle.b < 1 or len(puzzle.entries) != n * n or any(
        given < 0 or given > n for given in puzzle.entries
    ):
        raise ValueError('Invalid Sudoku puzzle')
    if domains is None:
        initial = initial_domains(puzzle)
        if initial is None:
            return SuffixGraphResult(0, SuffixGraphStats(0, 0, 0, 0, 0, 0, 0,
                                                         0, 0, 0, 0, 0, 0, 0))
    else:
        if len(domains) != n * n:
            raise ValueError('Incorrect domain vector length')
        initial = tuple(domains)
        full = (1 << n) - 1
        for cell, (mask, given) in enumerate(zip(initial, puzzle.entries)):
            if type(mask) is not int or not 0 < mask <= full:
                raise ValueError(f'Invalid domain at cell {cell}')
            if given and mask != (1 << (given - 1)):
                raise ValueError(f'Domain contradicts given at cell {cell}')

    base = 0
    free: list[int] = []
    options: dict[int, tuple[int, ...]] = {}
    for cell, mask in enumerate(initial):
        possibilities = tuple(
            candidate_bits(cell, digit, n, puzzle.b)
            for digit in range(n) if mask & (1 << digit)
        )
        if len(possibilities) == 1:
            if base & possibilities[0]:
                return SuffixGraphResult(0, SuffixGraphStats(0, 0, 0, 0, 0, 0,
                                                             0, 0, 0, 0, 0, 0, 0, 0))
            base |= possibilities[0]
        else:
            free.append(cell)
            options[cell] = possibilities
    if len(free) > limits.max_recursive_cells:
        raise FrontierCapacityError('Suffix recursion depth limit')
    future = [0] * (len(free) + 1)
    for pos in range(len(free) - 1, -1, -1):
        future[pos] = future[pos + 1]
        for choice in options[free[pos]]:
            future[pos] |= choice

    # Each layer has its own automorphism subgroup of the *remaining* graph.
    generators: list[tuple[tuple[int, ...], ...]] = []
    graph_examined = 0
    for pos in range(len(free)):
        perms: list[tuple[int, ...]] = []
        if mode != 'none':
            perms.extend(_geometric_generators(puzzle, free[pos:], initial))
        if mode == 'incidence':
            discovered, examined = _incidence_generators(
                free[pos:], options, 3 * n * n, limits)
            graph_examined += examined
            perms.extend(discovered)
        unique = tuple(dict.fromkeys(perms))[:limits.max_generators]
        generators.append(unique)

    memo: dict[tuple[int, int], int] = {}
    orbit_cache: list[dict[int, int]] = [{} for _ in range(len(free))]
    per_depth: dict[int, int] = {}
    hits = transitions = compatible = canonical_queries = nontrivial = 0
    examined_orbit = 0
    orbit_cache_entries = 0
    estimated_entry_bytes = 224 + 2 * ((3 * n * n + 7) // 8)

    def canonical(pos: int, signature: int) -> int:
        nonlocal canonical_queries, nontrivial, examined_orbit, orbit_cache_entries
        canonical_queries += 1
        cache = orbit_cache[pos]
        stored = cache.get(signature)
        if stored is not None:
            if stored != signature:
                nontrivial += 1
            return stored
        candidates = generators[pos]
        if not candidates:
            return signature
        orbit = {signature}
        stack = [signature]
        while stack:
            state = stack.pop()
            examined_orbit += 1
            for permutation in candidates:
                image = _transform(state, permutation)
                if image not in orbit:
                    if len(orbit) >= limits.max_orbit:
                        raise FrontierCapacityError('Suffix automorphism orbit limit')
                    orbit.add(image)
                    stack.append(image)
        representative = min(orbit)
        if representative != signature:
            nontrivial += 1
        if orbit_cache_entries + len(orbit) > limits.max_orbit_cache_entries:
            raise FrontierCapacityError('Suffix automorphism cache limit')
        if (len(memo) + orbit_cache_entries + len(orbit)) * estimated_entry_bytes > limits.frontier.max_estimated_bytes:
            raise FrontierCapacityError('Suffix graph estimated-byte limit')
        for state in orbit:
            cache[state] = representative
        orbit_cache_entries += len(orbit)
        return representative

    def recurse(pos: int, signature: int) -> int:
        nonlocal hits, transitions, compatible
        if pos == len(free):
            return 1
        signature &= future[pos]
        key = (pos, canonical(pos, signature))
        previous = memo.get(key)
        if previous is not None:
            hits += 1
            return previous
        if len(memo) + 1 > limits.frontier.max_states:
            raise FrontierCapacityError('Suffix graph memo state limit')
        # Insertion before expansion ensures the declared memory estimate also
        # covers the recursion stack, although it is not an RSS guarantee.
        if (len(memo) + orbit_cache_entries + 1) * estimated_entry_bytes > limits.frontier.max_estimated_bytes:
            raise FrontierCapacityError('Suffix graph estimated-byte limit')
        memo[key] = 0
        per_depth[pos] = per_depth.get(pos, 0) + 1
        total = 0
        for candidate in options[free[pos]]:
            transitions += 1
            if transitions > limits.frontier.max_transitions:
                raise FrontierCapacityError('Suffix graph transition limit')
            if key[1] & candidate:
                continue
            compatible += 1
            total += recurse(pos + 1, (key[1] | candidate) & future[pos + 1])
        memo[key] = total
        return total

    count = recurse(0, base & future[0])
    return SuffixGraphResult(count, SuffixGraphStats(
        fixed_cells=n * n - len(free), free_cells=len(free),
        memo_states=len(memo), memo_hits=hits, transitions=transitions,
        compatible_transitions=compatible,
        peak_states_at_depth=max(per_depth.values(), default=0),
        canonical_queries=canonical_queries,
        nontrivial_canonicalizations=nontrivial,
        orbit_elements_examined=examined_orbit,
        layers_with_generators=sum(bool(g) for g in generators),
        max_generators_at_layer=max(map(len, generators), default=0),
        graph_isomorphisms_examined=graph_examined,
        orbit_cache_entries=orbit_cache_entries,
    ))
