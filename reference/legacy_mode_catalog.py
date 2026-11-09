"""Independent legacy mode descriptor generator, for controlled exact A/B tests.

This reproduces the old b+1 catalog, before rowwise 2-adic valuation
pruning. Never use as a production default, and never infer asymptotic
runtime bounds from this reference implementation.
"""
from __future__ import annotations

from non_exponential_sudoku.core.algebra import v2
from non_exponential_sudoku.core.modes import Mode
from non_exponential_sudoku.core.network import Network
from non_exponential_sudoku.core.packing import Packing
from non_exponential_sudoku.runtime.budget import CapacityError


def original_catalog(net: Network, packing: Packing, t: int, p: int,
                     max_modes: int | None = None, *,
                     max_catalog_bytes: int = 128*1024*1024) -> list[Mode]:
    """Independent pre-optimization mode generator with original b+1 weight."""
    i = v2(t)
    left = {edge: k for k, vertex in enumerate(net.left) for edge in vertex.ports}
    right = {edge: k for k, vertex in enumerate(net.right) for edge in vertex.ports}
    result: list[Mode] = []
    for packet_id, packet in enumerate(packing.packets):
        rows = [(x, packing.groups_left[left[edge]][i])
                for x, edge in enumerate(packet.slots) if edge is not None]
        columns = [(y, edge, packing.groups_right[right[edge]][i])
                   for y, edge in enumerate(packet.slots) if edge is not None]
        for y0 in range(1 << (i + 1)):
            tile = [(edge, (y-y0) // (1 << (i+1)), g)
                    for y, edge, g in columns if y % (1 << (i+1)) == y0]
            if not tile:
                continue
            source = tile[0][2]
            target_rows = tuple(x for x, group in rows if group != source)
            if not target_rows:
                continue
            target = next(group for x, group in rows if x in target_rows)
            for b in range(p-1):
                if b > 0 and not any(j > 0 for _, j, _ in tile):
                    break
                if max_modes is not None and len(result) >= max_modes:
                    raise CapacityError('Mode catalog resource limit')
                result.append(Mode(
                    packet_id, y0, b, source, target, b+1,
                    tuple((edge, j) for edge, j, _ in tile), target_rows,
                ))
    return result

