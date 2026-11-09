#!/usr/bin/env python3
"""Generalized Sudoku tensor contractions and explicitly conditioned subinstances.

Conditioning wires is the substitution T_v(x_fixed, x_free) at every vertex.
It does not use Sudoku search, and it preserves the number of completions
with those wire values. The paper's contractor (not a replacement solver)
contracts the resulting smaller network.
"""
from __future__ import annotations
from non_exponential_sudoku import ContractionEngine, ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig
import argparse
import itertools
import json
import time
from dataclasses import asdict
from pathlib import Path
from non_exponential_sudoku.sudoku.three_cnf import Puzzle
from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.sudoku.encoding import sudoku_network
from non_exponential_sudoku.runtime.budget import CapacityError


def canonical_solution(box: int) -> tuple[int, ...]:
    n = box * box
    answer = tuple((r * box + r // box + c) % n + 1
                   for r in range(n) for c in range(n))
    assert Puzzle(box, (0,)*(n*n)).valid_solution(answer)
    return answer


def conditioned_network(puzzle: Puzzle, witness: tuple[int, ...],
                        free_cell_bits: dict[int, set[int]],
                        representation: str='band') -> Network:
    """Retain exactly the chosen bit's three independent Sudoku-network wires.

    Every fixed wire is substituted into BOTH endpoint tensors, with no
    elimination of unfixed assignments. Scalars are retained if nontrivial.
    """
    if not puzzle.valid_solution(witness):
        raise ValueError('Witness must satisfy puzzle including clues')
    if representation=='band':
        from reference.band_network import BandNetwork
        source=BandNetwork.from_puzzle(puzzle)
        old=source.net
        edge_cells=source.edge_cells
    elif representation=='direct':
        from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
        source=DirectNetwork.from_puzzle(puzzle)
        old=sudoku_network(puzzle)
        edge_cells=source.edge_cells
    else:
        raise ValueError('Unknown input encoding')
    n = puzzle.side
    t = max(1, (n - 1).bit_length())
    free_cells = {c: set(bits) for c,bits in free_cell_bits.items()}
    for c, bits in free_cells.items():
        if not 0 <= c < n*n or any(not 0 <= bit < t for bit in bits):
            raise ValueError('Free bit outside Sudoku grid/digit')
    retained = []
    original_bits = {}
    for edge,(cell,bit) in enumerate(edge_cells):
        original_bits[edge] = ((witness[cell]-1)>>bit)&1
        if bit in free_cells.get(cell, ()):
            retained.append(edge)
    old_to_new = {edge:i for i,edge in enumerate(retained)}

    def restrict(vertex: Vertex):
        local_free = tuple(e for e in vertex.ports if e in old_to_new)
        free_pos = tuple(old_to_new[e] for e in local_free)
        port_bits = tuple(None if e in old_to_new else original_bits[e]
                          for e in vertex.ports)
        positions = tuple(i for i, b in enumerate(port_bits) if b is None)
        fixed = tuple(0 if b is None else b for b in port_bits)
        original_oracle = vertex.oracle
        def oracle(bits, R):
            if len(bits) != len(positions): raise ValueError('Bit count mismatch')
            materialized = list(fixed)
            for pos,bit in zip(positions,bits):materialized[pos]=bit
            return original_oracle(tuple(materialized),R)
        return Vertex(vertex.name,free_pos,oracle)

    net=Network([restrict(v) for v in old.left],
                [restrict(v) for v in old.right],len(retained))
    net.validate()
    return net


def independently_count_conditioned(puzzle: Puzzle, witness: tuple[int, ...],
                                    free_cell_bits: dict[int,set[int]]):
    """Independent CELL-domain enumeration, not the tensor contractor.

    This is test-only; it never supplies results to the recursive algorithm.
    """
    n=puzzle.side
    varying=sorted(c for c,b in free_cell_bits.items() if b)
    domains=[]
    for cell in varying:
        mask=sum(1<<b for b in free_cell_bits[cell])
        w=witness[cell]-1
        domains.append([v+1 for v in range(n) if ((v ^ w)&~mask)==0])
    out=0
    for choices in itertools.product(*domains):
        candidate=list(witness)
        for cell,v in zip(varying,choices):candidate[cell]=v
        if puzzle.valid_solution(tuple(candidate)):out+=1
    return out


def fixtures():
    for b in (1,2,3,4):
        n=b*b
        blank=Puzzle(b,(0,)*(n*n))
        w=canonical_solution(b)
        yield f'{n}x{n}-one-bit',blank,w,{0:{0}},1
    # Four swaps, each 1<->3: the high bit of one digit is free.
    # Two complete 4x4 solutions survive, not merely a single witness.
    b=2; blank=Puzzle(b,(0,)*16);w=canonical_solution(b)
    yield '4x4-intercalate-two-solutions',blank,w,{c:{1} for c in (0,2,4,6)},2
    # Same pair of solutions can be tested by independently fixing two
    # of the four cells, leaving a real, four-wire? one-digit constraint.
    yield '4x4-intercalate-pair',blank,w,{c:{1} for c in (0,2)},1


def benchmark_fixture(name,puzzle,witness,free,expected,mode='micro',precision=None,
                      max_seconds=None,leaf_limit=18, micro_depth=1,leaf_strategy="eliminate",
                      representation="band"):
    from non_exponential_sudoku.sudoku.direct_network import DirectNetwork
    network=conditioned_network(puzzle,witness,free,representation)
    oracle_count=independently_count_conditioned(puzzle,witness,free)
    if oracle_count != expected: raise AssertionError((name,expected,oracle_count))
    p=precision or (network.edges + 1)
    labels=None
    if puzzle.b==1 and mode=='micro':
        # 1 retained bit has 3 edges; using crossing labels exercises modes.
        labels=(tuple((0,) for _ in network.left),
                tuple((1,) for _ in network.right))
    contractor=ContractionEngine(ContractorConfig(max(1,network.edges), p, schedule=mode, leaf=LeafConfig(limit=leaf_limit, strategy=leaf_strategy), micro_active_depth=micro_depth, root_labels=labels))
    start=time.perf_counter()
    try:
        value=contractor.contract(network)
        status='verified' if value[0]==oracle_count and all(v==0 for v in value[1:]) else 'mismatch'
        actual=value[0]
    except CapacityError as exc:
        status='capacity_refusal';actual=None;message=str(exc)
    duration=time.perf_counter()-start
    result={'fixture':name,'side':puzzle.side,'raw_wires':DirectNetwork.from_puzzle(puzzle).edge_count,
            'conditioned_wires':network.edges,'representation':representation,'expected_count':oracle_count,
            'actual_count':actual,'status':status,'schedule':mode,
            'seconds':round(duration,6),'leaf_strategy':leaf_strategy,'stats':asdict(contractor.stats)}
    if status=='capacity_refusal':result['reason']=message
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture',action='append',help='Run only a named fixture; repeatable')
    parser.add_argument('--schedule',choices=('micro','geometry64','paper'),default='micro')
    parser.add_argument('--leaf-limit',type=int,default=18)
    parser.add_argument('--leaf-strategy',choices=('enumerate','eliminate'),default='eliminate')
    parser.add_argument('--encoding',choices=('band','direct'),default='band')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    out=[]
    for name,puzzle,witness,free,expected in fixtures():
        if args.fixture and name not in args.fixture:continue
        result=benchmark_fixture(name,puzzle,witness,free,expected,
                                 mode=args.schedule,leaf_limit=args.leaf_limit,
                                 leaf_strategy=args.leaf_strategy,
                                 representation=args.encoding)
        print(json.dumps(result),flush=True)
        out.append(result)
    if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
