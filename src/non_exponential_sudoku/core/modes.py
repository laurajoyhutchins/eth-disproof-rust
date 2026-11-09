from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from collections.abc import Iterator
from .network import Network
from .packing import Packing
from math import ceil, comb
from sys import getsizeof
from .algebra import v2
from ..runtime.budget import CapacityError

@dataclass(frozen=True)
class Mode:
    packet: int
    y0: int
    b: int
    source: int
    target: int
    weight: int
    # For source tile, indexed by (original parent edge, integer j).
    tile: tuple[tuple[int,int], ...]
    # Row slots that can use this mode; coefficient computed on demand.
    rows: tuple[int,...]


def mode_catalog(net: Network, packets: Packing, t: int, p: int,
                 max_modes: int | None = None, *,
                 max_catalog_bytes: int = 128 * 1024 * 1024) -> list[Mode]:
    """Enumerate modes under a byte budget, without a global mode-count ceiling.

    The estimate includes each owned mode, its dictionary, tile tuples, and
    row tuple. Shared parent geometry and integer objects are not charged.
    It is a conservative accounting guard, not a process RSS guarantee.
    """
    if max_modes is not None and (type(max_modes) is not int or max_modes < 1):
        raise ValueError('Mode count limit must be positive or None')
    if type(max_catalog_bytes) is not int or max_catalog_bytes < 1:
        raise ValueError('Mode catalog byte budget must be positive')
    i=v2(t); a=packets.a; L=1<<a
    modes: list[Mode] = []
    used_bytes=0
    ol={edge:j for j,v in enumerate(net.left) for edge in v.ports}
    or_={edge:j for j,v in enumerate(net.right) for edge in v.ports}
    for k,packet in enumerate(packets.packets):
        rows=[(x,edge,packets.groups_left[ol[edge]][i]) for x,edge in enumerate(packet.slots) if edge is not None]
        cols=[(y,edge,packets.groups_right[or_[edge]][i]) for y,edge in enumerate(packet.slots) if edge is not None]
        for y0 in range(1<<(i+1)):
            tile=[(edge,(y-y0)//(1<<(i+1)),g) for y,edge,g in cols if y%(1<<(i+1))==y0]
            if not tile: continue
            source=tile[0][2]
            assert all(g==source for _,_,g in tile)
            target_rows=[x for x,_,g in rows if g!=source]
            if not target_rows: continue
            target=next(g for x,_,g in rows if x in target_rows)
            assert all(g==target for x,_,g in rows if x in target_rows)
            for b in range(p-1):
                if b>0 and not any(j>0 for _,j,_ in tile): break
                if max_modes is not None and len(modes) >= max_modes:
                    raise CapacityError('Mode catalog resource limit')
                mode=Mode(k,y0,b,source,target,b+1,
                          tuple((edge,j) for edge,j,_ in tile),tuple(target_rows))
                owned_bytes=(getsizeof(mode) + getsizeof(mode.__dict__)
                             + getsizeof(mode.tile) + getsizeof(mode.rows)
                             + sum(getsizeof(entry) for entry in mode.tile) + 8)
                if used_bytes + owned_bytes > max_catalog_bytes:
                    raise CapacityError('Mode catalog estimated-byte limit')
                used_bytes += owned_bytes
                modes.append(mode)
    return modes


def weighted_tuples(modes: list[Mode], p: int) -> Iterator[tuple[int, ...]]:
    """Iterative DFS of paper's weighted partitions, O(number of modes) space.

    Python recursion depth must not limit the theorem's mode enumeration;
    every partial assignment has an all-zero completion. No tuple cache.
    """
    n=len(modes)
    if n==0:
        yield ()
        return
    beta=[0]*n
    remaining=[p-1]*(n+1)
    maximum=[0]*n
    index=0
    maximum[0]=min(remaining[0]//modes[0].weight,len(modes[0].rows))
    while index>=0:
        if beta[index]>maximum[index]:
            beta[index]=0
            index-=1
            if index>=0:beta[index]+=1
            continue
        remaining[index+1]=remaining[index]-modes[index].weight*beta[index]
        if index==n-1:
            yield tuple(beta)
            beta[index]+=1
        else:
            index+=1
            beta[index]=0
            maximum[index]=min(remaining[index]//modes[index].weight,len(modes[index].rows))
