"""TDD of actual catalog and component-planning loops, including deep paths."""
from __future__ import annotations

from collections import deque
from sys import getsizeof

import pytest

from non_exponential_sudoku.contraction.children import child_components
from non_exponential_sudoku.contraction.planning import (
    ComponentCapacityExceeded, build_factorization_plan,
)
from non_exponential_sudoku.core.modes import Mode, mode_catalog
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.packing import Packet, Packing, pack, audit_packing
from reference.catalog_planning_work import catalog_planning_work, mode_owned_byte_ceiling

pytestmark = pytest.mark.checkpoint


def matched_packet() -> tuple[Network, Packing]:
    """Four orientation slots form a real fully occupied, audited packet."""
    one = lambda bits, ring: ring.one
    net = Network(
        [Vertex(str(j), (j,), one) for j in range(4)],
        [Vertex(str(j), (j,), one) for j in range(4)], 4,
    )
    labels = (
        tuple((j & 1, (j >> 1) & 1) for j in range(4)),
        tuple((1 - (j & 1), 1 - ((j >> 1) & 1)) for j in range(4)),
    )
    packing = pack(net, 2, 2, labels)
    assert all(audit_packing(net, packing)[key] for key in (
        'all_edges_packed_exactly_once', 'orientation_geometry_valid',
        'packet_bound_met', 'group_load_bound_met',
    ))
    return net, packing


@pytest.mark.parametrize('precision', (1, 2, 3, 4, 8, 12, 19))
def test_catalog_modes_and_estimated_guard_covered(precision: int) -> None:
    net, packing = matched_packet()
    envelope = catalog_planning_work(
        edges=net.edges, vertices=len(net.left)+len(net.right),
        packets=len(packing.packets), slots=1<<packing.a,
        groups=packing.r, active_coordinates=1, center_valuation=0,
        precision=precision,
    )
    modes = mode_catalog(net, packing, 1, precision, max_catalog_bytes=max(1,envelope.catalog_limit))
    assert len(modes) <= envelope.mode_count_ceiling
    observed_bytes = 0
    for mode in modes:
        owned = (getsizeof(mode) + getsizeof(mode.__dict__)
                 + getsizeof(mode.tile) + getsizeof(mode.rows)
                 + sum(getsizeof(entry) for entry in mode.tile) + 8)
        assert owned <= mode_owned_byte_ceiling(4)
        observed_bytes += owned
        assert mode.weight >= 1
        assert len(mode.rows) <= envelope.slots and len(mode.tile) <= envelope.slots
    assert observed_bytes <= envelope.catalog_limit
    assert len(modes) <= 2 * max(0, precision-1)


def path_topology(n: int, *, disconnected: bool = False) -> tuple[Network, Packing]:
    """A valid incidence topology, not a claim of paper-admitted packing."""
    one = lambda bits, ring: ring.one
    left: list[list[int]] = [[] for _ in range(n)]
    right: list[list[int]] = [[] for _ in range(n)]
    edges = 0
    for j in range(n):
        left[j].append(edges)
        right[j].append(edges)
        edges += 1
        if j + 1 < n and not disconnected:
            left[j + 1].append(edges)
            right[j].append(edges)
            edges += 1
    net = Network(
        [Vertex(f'L{j}', tuple(ports), one) for j, ports in enumerate(left)],
        [Vertex(f'R{j}', tuple(ports), one) for j, ports in enumerate(right)],
        edges,
    )
    net.validate()
    pk = Packing(
        tuple((0, 0) for _ in left), tuple((0, 0) for _ in right),
        ([Packet(tuple(range(start, min(start+4, edges))) + (None,) * (4-min(4,edges-start)), ((0,0),(0,0)))
          for start in range(0,edges,4)] if disconnected else
         [Packet((edge, None, None, None), ((0,0),(0,0))) for edge in range(edges)]),
        2, 2, 4,
    )
    return net, pk


def independent_components(net: Network, packing: Packing, group: int, coordinate: int) -> set[tuple[tuple[int, ...], tuple[tuple[str, int], ...]]]:
    """Reference BFS over endpoint-to-packet links; no union-find."""
    for_edge = {e: k for k, pkt in enumerate(packing.packets) for e in pkt.slots if e is not None}
    adjacency: dict[tuple[str,int], set[tuple[str,int]]] = {}
    for side, vertices, labels in (
        ('Y', net.left, packing.groups_left), ('X', net.right, packing.groups_right)
    ):
        for j, v in enumerate(vertices):
            if labels[j][coordinate] != group:
                continue
            v_key = (side, j)
            adjacency.setdefault(v_key, set())
            for edge in v.ports:
                p_key = ('P', for_edge[edge])
                adjacency[v_key].add(p_key)
                adjacency.setdefault(p_key, set()).add(v_key)
    seen: set[tuple[str,int]] = set()
    components: set[tuple[tuple[int, ...], tuple[tuple[str, int], ...]]] = set()
    for start in adjacency:
        if start in seen:
            continue
        seen.add(start)
        todo = deque([start])
        part: set[tuple[str,int]] = set()
        while todo:
            node = todo.popleft()
            part.add(node)
            for neighbor in adjacency[node]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    todo.append(neighbor)
        p = tuple(sorted(i for kind,i in part if kind == 'P'))
        kept_nodes = tuple(sorted((kind,i) for kind,i in part if kind != 'P'))
        components.add((p, kept_nodes))
    return components


@pytest.mark.parametrize('disconnected', (False, True))
@pytest.mark.parametrize('size', (1, 3, 15, 1400))
def test_union_find_matches_independent_bfs_even_beyond_recursion_limit(size: int, disconnected: bool) -> None:
    net, packing = path_topology(size, disconnected=disconnected)
    got = child_components(net, packing, 0, 0)
    assert {(c.packets, tuple(sorted(c.kept))) for c in got} == independent_components(net,packing,0,0)
    assert len(got) == (((size+3)//4) if disconnected else 1)


def test_factor_planning_complete_and_refusal_guard() -> None:
    net, packing = path_topology(68, disconnected=True)
    modes = [Mode(0, 0, 0, 0, 1, 1, (), (0,)), Mode(1, 0, 0, 0, 1, 1, (), (0,))]
    affected = {0: (0, 1)}
    with pytest.raises(ComponentCapacityExceeded):
        build_factorization_plan(net, packing, modes, 0, {0}, affected,
                                 strategy='components', max_components=16)
    envelope = catalog_planning_work(
        edges=net.edges, vertices=len(net.left)+len(net.right),
        packets=len(packing.packets), slots=4, groups=2,
        active_coordinates=1, center_valuation=0, precision=4,
    )
    plan = build_factorization_plan(
        net, packing, modes, 0, {0}, affected,
        strategy='components', max_components=envelope.component_limit,
    )
    assert len(plan.factors) == 17
    assert sum(tuple(s.mode_indices).count(0) for s in plan.factors) == 1
    assert sum(tuple(s.mode_indices).count(1) for s in plan.factors) == 1
    assert {k for factor in plan.factors for k in factor.mode_indices} == {0, 1}
    assert len(plan.factors) <= envelope.component_limit
    whole = build_factorization_plan(
        net, packing, modes, 0, {0}, affected, strategy='whole', max_components=1,
    )
    assert len(whole.factors) == 1
    assert whole.factors[0].mode_indices == (0, 1)


def test_real_mode_scopes_are_partitioned_exactly() -> None:
    net, packing = matched_packet()
    modes = mode_catalog(net, packing, 1, 8)
    occupied = {0, 1}
    affected = {group: tuple(j for j,m in enumerate(modes) if group in (m.source,m.target))
                for group in occupied}
    for strategy in ('whole','components'):
        plan=build_factorization_plan(net,packing,modes,0,occupied,affected,strategy=strategy,max_components=100)
        for group in occupied:
            got = sorted(j for f in plan.factors if f.group == group for j in f.mode_indices)
            assert got == sorted(affected[group])


def test_symbolic_paper_scale_catalog_planning_is_polynomial_work() -> None:
    for lam in (131072, 262144, 524288):
        s = (1 << (lam-1)) + 1
        L = 4
        P = s // L
        envelope = catalog_planning_work(
            edges=s, vertices=s, packets=P, slots=L, groups=64,
            active_coordinates=1, center_valuation=0, precision=s,
            input_name_bits=lam,
        )
        assert envelope.mode_count_ceiling <= P * 2 * s
        assert envelope.catalog_limit > envelope.mode_count_ceiling
        # A polynomial in s has logarithmic cost O(log s), even though its
        # numerical budget is far beyond physical memory.
        assert envelope.schoolbook_bit_work_majorant.bit_length() < 40*lam


def test_invalid_premises_refuse_symbolic_certificate() -> None:
    base=dict(edges=8,vertices=8,packets=3,slots=4,groups=64,
              active_coordinates=1,center_valuation=0,precision=5)
    bad = (dict(slots=3), dict(active_coordinates=2), dict(center_valuation=1),
           dict(packets=7), dict(edges=-1), dict(precision=0), dict(vertices=2.0))
    for mutation in bad:
        with pytest.raises(ValueError):
            catalog_planning_work(**(base | mutation))


def test_measured_guard_budget_never_claims_finite_ram_capacity() -> None:
    env = catalog_planning_work(edges=4,vertices=8,packets=1,slots=4,
         groups=64, active_coordinates=1,center_valuation=0,precision=12)
    assert env.catalog_guard_bytes > 0 and env.component_limit > 0
    assert env.total_outer_steps > 0


def test_catalog_and_planning_costs_are_charged_in_whole_frame() -> None:
    from non_exponential_sudoku.runtime.config import ContractorConfig, ModeConfig
    from reference.whole_frame_recurrence import assemble_paper_recurrence, UnclosedRecurrence

    s = (1 << 131071) + 1
    cfg = ContractorConfig(
        s=s, precision=33, schedule='paper',
        mode=ModeConfig(native_sparse=False),
    )
    result = assemble_paper_recurrence(
        cfg, edges=s, vertices=s, input_name_bits=128,
    )
    assert result.frames[-1].log2_catalog_planning_bit_work_ceiling == 0
    for frame in result.frames[:-1]:
        assert frame.log2_catalog_planning_bit_work_ceiling > 0
        assert (frame.log2_named_local_work_ceiling
                >= frame.log2_catalog_planning_bit_work_ceiling)
    with pytest.raises(UnclosedRecurrence):
        result.require_complete_theorem()
