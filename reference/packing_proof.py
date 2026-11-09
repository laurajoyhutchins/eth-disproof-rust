"""Independent, exact witnesses for the conditional-expectation packing argument.

Not used by the production solver. The slow oracle operates on *ordered
pairs of edges* and has no knowledge of production's sparse greedy scores.
The summary certificate needs only counts, not an exponential label universe.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import asdict, dataclass

from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.core.packing import Packing, audit_packing


def edge_owners(net: Network) -> tuple[tuple[int, ...], tuple[int, ...]]:
    left = [-1] * net.edges
    right = [-1] * net.edges
    for side, owners in ((net.left, left), (net.right, right)):
        for i, vertex in enumerate(side):
            for e in vertex.ports:
                if not 0 <= e < net.edges or owners[e] != -1:
                    raise ValueError("invalid bipartite incidence")
                owners[e] = i
    if -1 in left or -1 in right:
        raise ValueError("some edge is missing a port")
    return tuple(left), tuple(right)


def conditional_objective_numerator(
    net: Network, alphabet: int,
    left_assigned: tuple[int, ...], right_assigned: tuple[int, ...],
) -> int:
    """Return D*E[sum_gamma (X_gamma-M/D)^2 | assigned vertices].

    D=alphabet**2. Unassigned vertices are independent uniform labels.
    Multiply per-side equality probabilities with denominator `alphabet`;
    the two sides are independent, so this integer is exact. Complexity is
    quadratic in the edge count and intended only for small oracle tests.
    """
    if alphabet < 1:
        raise ValueError("alphabet must be positive")
    if len(left_assigned) > len(net.left) or len(right_assigned) > len(net.right):
        raise ValueError("too many assigned labels")
    if any(not 0 <= x < alphabet for x in left_assigned + right_assigned):
        raise ValueError("invalid assigned label")
    left_owner, right_owner = edge_owners(net)

    def equality_numerator(i: int, j: int, owners: tuple[int, ...], assigned: tuple[int, ...]) -> int:
        u, v = owners[i], owners[j]
        if u == v:
            return alphabet
        if u >= len(assigned) or v >= len(assigned):
            return 1
        return alphabet if assigned[u] == assigned[v] else 0

    pairs = sum(
        equality_numerator(i, j, left_owner, left_assigned)
        * equality_numerator(i, j, right_owner, right_assigned)
        for i in range(net.edges) for j in range(net.edges)
    )
    return pairs - net.edges ** 2


@dataclass(frozen=True)
class PackingProofRecord:
    edges: int
    maximum_degree: int
    alphabet: int
    label_pairs: int
    packet_width: int
    initial_objective_numerator: int
    final_objective_numerator: int
    generic_objective_bound_numerator: int
    greedy_objective_bound_met: bool
    maximum_pair_load: int
    padded_pair_load: int
    packet_count: int
    padded_full_alphabet_packet_count: int
    maximum_side_coordinate_load: int
    numerical_hypotheses_met: bool
    padding_bound_met: bool
    packet_bound_met: bool
    coordinate_bound_met: bool
    edges_packed_once: bool
    orientation_geometry_valid: bool

    def as_record(self) -> dict[str, int | bool]:
        return asdict(self)


def packing_proof_record(net: Network, packed: Packing) -> PackingProofRecord:
    """Recompute the lemma's integer inequalities from the *actual* packing.

    This is a witness, not a substitute for the universal greedy proof.
    A numeric-hypothesis case must pass all inequalities; otherwise raise,
    rather than treating a failed implementation as a theorem counterexample.
    """
    net.validate()
    if packed.r < 1 or packed.a < 1:
        raise ValueError("invalid packing parameters")
    r, a = packed.r, packed.a
    alphabet = r ** a
    D = alphabet ** 2
    L = 1 << a
    if len(packed.groups_left) != len(net.left) or len(packed.groups_right) != len(net.right):
        raise ValueError("bad vertex label counts")
    if any(len(label) != a or any(d < 0 or d >= r for d in label)
           for label in packed.groups_left + packed.groups_right):
        raise ValueError("invalid vertex label")
    M = net.edges
    delta = max((len(vertex.ports) for vertex in net.left + net.right), default=0)
    lo, ro = edge_owners(net)
    classes = Counter((packed.groups_left[lo[e]], packed.groups_right[ro[e]]) for e in range(M))
    sum_squares = sum(count * count for count in classes.values())
    final_objective = D * sum_squares - M * M

    # Exact E[F] for independently uniformly labeled vertices. In ordered
    # pairs of edges, B pairs share both endpoints; Ls/Rs share a left/right
    # endpoint. Their equality probabilities are 1, 1/R, and 1/R**2.
    left_squares = sum(len(v.ports) ** 2 for v in net.left)
    right_squares = sum(len(v.ports) ** 2 for v in net.right)
    both_squares = sum(n * n for n in Counter(zip(lo, ro)).values())
    initial_objective = ((alphabet - 1) ** 2 * both_squares
                         + (alphabet - 1) * (left_squares + right_squares))
    generic_bound = 2 * M * delta * D
    max_class = max(classes.values(), default=0)
    Hpad = ((max_class + L - 1) // L) * L
    if Hpad != packed.max_load:
        raise AssertionError("padded load disagrees with actual packer")

    side_counts = [Counter() for _ in range(2 * a)]
    for e in range(M):
        for coord in range(a):
            side_counts[coord][packed.groups_left[lo[e]][coord]] += 1
            side_counts[a + coord][packed.groups_right[ro[e]][coord]] += 1
    peak_side = max((max(counter.values(), default=0) for counter in side_counts), default=0)
    numerical = (M >= 2 * D * D * delta and M >= L * D and 2 * L <= delta)
    bound_met = final_objective <= initial_objective <= generic_bound
    geometric_audit = audit_packing(net, packed)
    record = PackingProofRecord(
        M, delta, alphabet, D, L, initial_objective, final_objective,
        generic_bound, bound_met, max_class, Hpad, len(packed.packets),
        Hpad * D // L, peak_side, numerical, Hpad * D <= 3 * M,
        len(packed.packets) * L <= 3 * M, peak_side * r <= 3 * M,
        geometric_audit["all_edges_packed_exactly_once"],
        geometric_audit["orientation_geometry_valid"],
    )
    if not (record.edges_packed_once and record.orientation_geometry_valid):
        raise AssertionError("packing geometry does not preserve port incidence")
    if numerical and not (bound_met and record.padding_bound_met
                          and record.packet_bound_met and record.coordinate_bound_met):
        raise AssertionError("packing violates a consequence of the numerical hypotheses")
    return record
