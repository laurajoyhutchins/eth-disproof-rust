from __future__ import annotations

from dataclasses import dataclass
from collections import defaultdict
from itertools import product
from collections.abc import Sequence
from typing import Literal, TypedDict
from math import ceil, comb, isqrt, log2
from .network import Network

LabelCoordinates = tuple[tuple[int, ...], ...]
LabelPair = tuple[LabelCoordinates, LabelCoordinates]

class PackingAudit(TypedDict):
    all_edges_packed_exactly_once: bool
    orientation_geometry_valid: bool
    packet_count: int
    packet_bound_met: bool
    max_group_side_ports: int
    group_load_bound_met: bool

@dataclass(frozen=True)
class Packet:
    slots: tuple[int | None,...]  # slot -> original edge, or an unused slot
    symbols: tuple[tuple[int,int],...]


@dataclass
class Packing:
    groups_left: LabelCoordinates
    groups_right: LabelCoordinates
    packets: list[Packet]
    r: int
    a: int
    max_load: int


def balanced_labels(net: Network, r: int, a: int, *, tie_break: Literal['spread', 'numeric'] = 'spread') -> LabelPair:
    """Conditional-expectation labels with an objective-preserving tie break.

    The original sparse overlap scores are nonnegative. Before all r**a
    labels have been used, assigning a completely unused full label incurs
    zero additional overlap, which is a *global minimum* of the incremental
    conditional-expectation objective. We can therefore choose an unused label
    without even forming the overlap scores. This choice is not merely a
    heuristic: it attains the same minimum of the paper's objective.

    A smallest-index tie break chooses 0, 1, 2, ... and concentrates all
    early early labels in coordinate 1 (and later coordinates). A bijective
    coordinate-mixed sequence spreads each prefix of length r across *every*
    coordinate. After the complete label alphabet is exhausted, we minimize
    the unchanged sparse overlap objective, using coordinate load only to
    decide exact ties. ``numeric`` selects the smallest-index minimizer for differential tests.
    """
    if tie_break not in ('spread', 'numeric'):
        raise ValueError('tie_break must be spread or numeric')
    if r < 1 or a < 1:
        raise ValueError('r and a must be positive')
    R = r ** a
    left_owner = [-1] * net.edges
    right_owner = [-1] * net.edges
    for k, vertex in enumerate(net.left):
        for edge in vertex.ports:
            left_owner[edge] = k
    for k, vertex in enumerate(net.right):
        for edge in vertex.ports:
            right_owner[edge] = k
    if any(v < 0 for v in left_owner + right_owner):
        raise AssertionError('Network is not bipartite on every wire')

    powers = [r ** i for i in range(a)]

    def digits(k: int) -> tuple[int, ...]:
        return tuple((k // powers[i]) % r for i in range(a))

    def spread_label(index: int) -> int:
        # Invertible triangular map over Z/rZ. Full labels stay distinct,
        # while the first r labels cycle over every coordinate individually.
        d0 = index % r
        label = d0
        for i in range(1, a):
            di = (index // powers[i]) % r
            label += ((d0 + di) % r) * powers[i]
        return label

    def pick_numeric(scores: dict[int, int], occupied: set[int]) -> int:
        candidates = set(occupied)
        if len(occupied) < R:
            for k in range(len(occupied) + 1):
                if k not in occupied:
                    candidates.add(k)
                    break
        return min(candidates, key=lambda k: (scores.get(k, 0), k))

    def choose(scores: dict[int, int], labels: list[int], degree_load: list[defaultdict[int, int]]) -> int:
        occupied = set(labels)
        if tie_break == 'numeric':
            return pick_numeric(scores, occupied)
        if len(occupied) < R:
            # Incremental score = 0, provably minimal (all weights >= 0).
            return spread_label(len(occupied))
        return min(occupied, key=lambda k:
                   (scores.get(k, 0),
                    sum(degree_load[i].get(d, 0)
                        for i, d in enumerate(digits(k))), k))

    def add_load(load: list[defaultdict[int, int]], label: int, degree: int) -> None:
        for i, d in enumerate(digits(label)):
            load[i][d] += degree

    right_hist: list[defaultdict[int, int]] = []
    for vertex in net.left:
        counts: defaultdict[int, int] = defaultdict(int)
        for edge in vertex.ports:
            counts[right_owner[edge]] += 1
        right_hist.append(counts)
    labels_l: list[int] = []
    left_load: list[defaultdict[int, int]] = [defaultdict(int) for _ in range(a)]
    for j, vertex in enumerate(net.left):
        scores: defaultdict[int, int] = defaultdict(int)
        # With a free unused label, a minimum is known without scoring.
        if tie_break == 'numeric' or j >= R:
            for w in range(j):
                shared = sum(count * right_hist[w].get(x, 0)
                             for x, count in right_hist[j].items())
                weight = len(vertex.ports) * len(net.left[w].ports) + (R - 1) * shared
                scores[labels_l[w]] += weight
        label = choose(scores, labels_l, left_load)
        labels_l.append(label)
        add_load(left_load, label, len(vertex.ports))

    left_label_hists: list[defaultdict[int, int]] = []
    for vertex in net.right:
        counts = defaultdict(int)
        for edge in vertex.ports:
            counts[labels_l[left_owner[edge]]] += 1
        left_label_hists.append(counts)
    labels_r: list[int] = []
    right_load: list[defaultdict[int, int]] = [defaultdict(int) for _ in range(a)]
    for j, vertex in enumerate(net.right):
        scores = defaultdict(int)
        if tie_break == 'numeric' or j >= R:
            for w in range(j):
                overlap = sum(count * left_label_hists[w].get(lbl, 0)
                              for lbl, count in left_label_hists[j].items())
                scores[labels_r[w]] += overlap
        label = choose(scores, labels_r, right_load)
        labels_r.append(label)
        add_load(right_load, label, len(vertex.ports))
    return tuple(map(digits, labels_l)), tuple(map(digits, labels_r))


def pack(net: Network, r: int, a: int, labels: LabelPair | None = None) -> Packing:
    if a<1: raise ValueError('Need at least one coordinate to form Cauchy packets')
    L=1<<a
    if labels is None: labels=balanced_labels(net,r,a)
    labels_l,labels_r=labels
    if len(labels_l)!=len(net.left) or len(labels_r)!=len(net.right): raise ValueError('Bad label counts')
    owner_l={edge:i for i,v in enumerate(net.left) for edge in v.ports}
    owner_r={edge:i for i,v in enumerate(net.right) for edge in v.ports}
    classes: defaultdict[tuple[tuple[int, ...], tuple[int, ...]], list[int]] = defaultdict(list)
    for edge in range(net.edges):
        classes[(labels_l[owner_l[edge]],labels_r[owner_r[edge]])].append(edge)
    maximum=max((len(v) for v in classes.values()),default=0)
    Hpad=((maximum+L-1)//L)*L
    packets: list[Packet] = []
    # Only normalized pair-label families containing a real edge matter.
    # Every omitted family would have exclusively unused ports and hence
    # contributes a scalar one. This is exact even with 64 groups.
    pair_families={tuple((min(left[i],right[i]),max(left[i],right[i]))
                         for i in range(a)) for left,right in classes}
    for symbol_pairs in sorted(pair_families):
        # enumerate orientations in each packet, with 2^(a-a') copies of each ordered pair.
        per_class: defaultdict[tuple[tuple[int, ...], tuple[int, ...]], list[int]] = defaultdict(list)
        for x in range(L):
            l=[];h=[]
            for i,(lo,hi) in enumerate(symbol_pairs):
                if (x>>i)&1: l.append(hi);h.append(lo)
                else: l.append(lo);h.append(hi)
            per_class[(tuple(l),tuple(h))].append(x)
        group_slots=len(next(iter(per_class.values())))
        for packet_index in range(Hpad//group_slots):
            slots: list[int | None]=[None]*L
            for class_id,indices in per_class.items():
                edge_list=classes.get(class_id,[])
                for m,x in enumerate(indices):
                    k=packet_index*group_slots+m
                    if k<len(edge_list):slots[x]=edge_list[k]
            # Completely unused packets contribute the scalar one and may
            # be omitted exactly. This avoids millions of inert descriptions
            # in sparse microexamples without altering the paper identity.
            if any(edge is not None for edge in slots):
                packets.append(Packet(tuple(slots),tuple(symbol_pairs)))
    placed=sorted(edge for pkt in packets for edge in pkt.slots if edge is not None)
    if placed!=list(range(net.edges)):
        raise AssertionError(f'Packet packing missed/duplicated edges {placed}')
    return Packing(labels_l,labels_r,packets,r,a,Hpad)


def audit_packing(net: Network, packed: Packing) -> PackingAudit:
    """Check paper lemma's quantitative and geometric packet invariants.

    Returns explicit observations so a small demonstrator never silently
    pretends to meet the large-instance hypotheses.
    """
    M=net.edges; L=1<<packed.a;r=packed.r
    loc={edge:(k,x) for k,packet in enumerate(packed.packets)
         for x,edge in enumerate(packet.slots) if edge is not None}
    owner_left={edge:i for i,v in enumerate(net.left) for edge in v.ports}
    owner_right={edge:i for i,v in enumerate(net.right) for edge in v.ports}
    geometry=True
    for edge,(k,x) in loc.items():
        pairs=packed.packets[k].symbols
        left=packed.groups_left[owner_left[edge]]
        right=packed.groups_right[owner_right[edge]]
        for j,(lo,hi) in enumerate(pairs):
            target=(hi,lo) if (x>>j)&1 else (lo,hi)
            if (left[j],right[j])!=target:geometry=False
    group_load: defaultdict[tuple[int, int], list[int]] = defaultdict(lambda:[0,0])
    for edge in range(M):
        for i in range(packed.a):
            group_load[(i,packed.groups_left[owner_left[edge]][i])][0]+=1
            group_load[(i,packed.groups_right[owner_right[edge]][i])][1]+=1
    return {
        'all_edges_packed_exactly_once':len(loc)==M,
        'orientation_geometry_valid':geometry,
        'packet_count':len(packed.packets),
        'packet_bound_met':len(packed.packets)*L<=3*M,
        'max_group_side_ports':max((max(x) for x in group_load.values()),default=0),
        'group_load_bound_met':all(max(x)*r<=3*M for x in group_load.values()),
    }
