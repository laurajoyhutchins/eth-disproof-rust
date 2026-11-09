#!/usr/bin/env python3
"""Bounded-degree recursive-scaling audit of the genuine Appendix-D packet geometry.

Distinguishes structural child graphs (oracle-free, but matching make_child port
incidence), executable algebraic contraction, and the theorem's complexity claim.
All inputs are deterministic parity-factor networks independently countable by GF(2).
Run python scaling_experiment.py to generate benchmark_scaling_v9.json.
"""
from __future__ import annotations
from non_exponential_sudoku import ContractionEngine, ContractorConfig, LeafConfig, RecoveryConfig, ModeConfig
import argparse
import hashlib
import json
import os
import platform
import resource
import statistics
import subprocess
import sys
import time
import tracemalloc
from collections import defaultdict
from pathlib import Path

from non_exponential_sudoku.core.network import Network, Vertex
from non_exponential_sudoku.core.algebra import Padic, modulus_polynomial
from non_exponential_sudoku.runtime.budget import CapacityError
from non_exponential_sudoku.core.packing import pack, audit_packing
from non_exponential_sudoku.contraction.children import child_edge_audit, make_child
from non_exponential_sudoku.core.modes import mode_catalog


def parity_factor(rhs: int):
    def oracle(bits, ring, rhs=rhs):
        return ring.one if (sum(bits) & 1) == rhs else ring.zero
    return oracle


def parity_network(family: str, span: int, contradiction: bool = False) -> Network:
    """Degree-2 cycle, or degree-3 cyclic-ladder bipartite factor network.

    Each Boolean wire is incident to exactly two parity constraints.
    A connected consistent family has exactly 2**(M - V + 1) solutions.
    No Sudoku solver, search heuristic, or tensor contraction is used.
    """
    if span < 1:
        raise ValueError('span must be positive')
    degree = {'cycle2': 2, 'ladder3': 3, 'pair2': 2}[family]
    left_ports = [[] for _ in range(span)]
    right_ports = [[] for _ in range(span)]
    for i in range(span):
        for j in range(degree):
            edge = degree * i + j
            left_ports[i].append(edge)
            right_ports[(i if family=='pair2' else (i+j) % span)].append(edge)
    left = [Vertex('L'+str(i)+('!' if contradiction and i==0 else ''), tuple(p), parity_factor(int(contradiction and i==0)))
            for i, p in enumerate(left_ports)]
    right = [Vertex('R'+str(i), tuple(p), parity_factor(0))
             for i, p in enumerate(right_ports)]
    net = Network(left, right, degree * span)
    net.validate()
    return net


def independent_gf2_count(net: Network) -> tuple[int, int]:
    """Independent exact Gaussian elimination over GF(2); not tensor contraction.

    Inputs to this function are the deterministic parity_factor fixture family.
    RHS is read from the controlled fixture convention, not vertex oracles.
    """
    m = net.edges
    pivot = {}
    rows = 0
    # Contradictions are represented by suffix ! on left vertex names in
    # standalone generic benchmarks; for the generated families use lhs_rhs.
    for vertex in net.left + net.right:
        row = 0
        for k in vertex.ports:
            row ^= 1 << k
        rhs = 1 if vertex.name.endswith('!') else 0
        row |= rhs << m
        rows += 1
        while True:
            variables = row & ((1 << m) - 1)
            if variables == 0:
                if (row >> m) & 1:
                    return 0, len(pivot)
                break
            lead = (variables & -variables).bit_length()-1
            if lead in pivot:
                row ^= pivot[lead]
            else:
                pivot[lead] = row
                break
    return 1 << (m-len(pivot)), len(pivot)


def independent_count(family: str, span: int, contradiction: bool=False):
    net = parity_network(family,span,contradiction)
    # Independent RHS comes from fixture naming, never evaluating tensor oracles.
    return independent_gf2_count(net)


def topology_child(net: Network, packing, group: int, coordinate: int) -> Network:
    """The *exact* graph topology of make_child, independent of beta,t,z.

    No algebraic equivalence is claimed for its dummy packet oracles. This
    function is for graph size/degree/workload instrumentation ONLY.
    """
    packet_for = {}
    for packet_id, pkt in enumerate(packing.packets):
        for edge in pkt.slots:
            if edge is not None:
                packet_for[edge] = packet_id
    touched = defaultdict(list)
    kept = []
    next_edge = 0
    for side, vertices, labels in (('Y',net.left,packing.groups_left),
                                   ('X',net.right,packing.groups_right)):
        for vertex, label in zip(vertices, labels):
            if label[coordinate] != group:
                continue
            ports = []
            for parent_edge in vertex.ports:
                ports.append(next_edge)
                touched[packet_for[parent_edge]].append(next_edge)
                next_edge += 1
            kept.append(Vertex('keep:'+vertex.name,tuple(ports),vertex.oracle))
    def placeholder(bits, ring):
        raise RuntimeError('Topology-only packet oracle must not be evaluated')
    # Preserve zero-degree packet vertices. make_child does not remove them.
    packets = [Vertex('packet:'+str(i),tuple(touched.get(i,())),placeholder)
               for i in range(len(packing.packets))]
    child = Network(kept, packets, next_edge)
    child.validate()
    return child


def check_topology_against_real_child(net: Network, coordinate: int = 0):
    """Prove the structural extractor matches the executed child constructor."""
    packed=pack(net,64,2)
    ring=Padic(5,modulus_polynomial(5),7)
    labels=packed.groups_left+packed.groups_right
    candidate=next((i for i in range(64) if any(label[coordinate]==i for label in labels)),0)
    actual=make_child(net,packed,[],(),1,ring.zero,ring,candidate,coordinate)
    topo=topology_child(net,packed,candidate,coordinate)
    assert actual.edges == topo.edges
    assert [x.ports for x in actual.left] == [x.ports for x in topo.left]
    assert [x.ports for x in actual.right] == [x.ports for x in topo.right]
    return candidate



def mode_catalog_projection(net: Network, packed, precision: int):
    """Independent exact count of t=1 modes, without constructing descriptors.

    At i=v2(1)=0, every admissible crossing slot has v2(1-y0+x)=0.
    Each nonzero b-mode therefore has certified weight (a+1)+b,
    rather than the old b+1. The count is an arithmetic formula for
    each tile; no coefficient arrays or p-sized mode list are needed.
    """
    owner_left={edge:j for j,v in enumerate(net.left) for edge in v.ports}
    owner_right={edge:j for j,v in enumerate(net.right) for edge in v.ports}
    total=0
    first_weight=0
    high_tiles=0
    base_weights=[]
    a=packed.a
    for pkt in packed.packets:
        rows=[(x,edge,packed.groups_left[owner_left[edge]][0])
              for x,edge in enumerate(pkt.slots) if edge is not None]
        cols=[(y,edge,packed.groups_right[owner_right[edge]][0])
              for y,edge in enumerate(pkt.slots) if edge is not None]
        for y0 in (0,1):
            tile=[(y,edge,g) for y,edge,g in cols if y%2==y0]
            if not tile: continue
            source=tile[0][2]
            assert all(g==source for _,_,g in tile)
            target_slots=[x for x,_,g in rows if g!=source]
            if not target_slots: continue
            assert all(g==next(g0 for x0,_,g0 in rows if x0==target_slots[0])
                       for x,_,g in rows if x in target_slots)
            # A valid crossing at i=0 has odd displacement, so v=0.
            assert all((1-y0+x)%2 for x in target_slots)
            base=a+1
            high=any(y>=2 for y,_,_ in tile)
            high_tiles+=int(high)
            if base>=precision: continue
            # b=0,...,(p-1-base) when high; only b=0 otherwise.
            count=precision-base if high else 1
            total+=count
            first_weight+=int(base==1)
            base_weights.append(base)

    # Select a small prefix of b=0 modes whose *joint* weight fits.
    # Every subset of these modes is admissible (each has row cap >=1),
    # so there are at least 2**prefix independent binary tuples.
    weight_sum=0
    binary_modes=0
    for weight in sorted(base_weights):
        if weight_sum+weight>=precision:break
        weight_sum+=weight
        binary_modes+=1
    return {'t':1,'precision_bits':precision,
            'exact_descriptor_count':total,
            'weight_one_modes':first_weight,
            'high_order_tiles':high_tiles,
            'at_least_binary_mode_tuple_log2':binary_modes,
            'reason':'A prefix of independent b=0 modes has total certified weight below precision; its subsets yield a lower bound.'}

def summarize_level(level: int, networks: list[Network], *, expand: bool=False,
                    full_packing: bool=True):
    """One complete geometry level, without evaluating coefficients."""
    tick=time.perf_counter()
    tracemalloc.start()
    nodes=[]
    next_networks=[]
    child_wire_total=0
    candidate_child_count=0
    active_child_count=0
    group_zero_edges=0
    packet_count=0
    maximum_child=0
    maximum_child_degree=0
    edge_conservation=True
    all_shrink=True
    packet_passes=0
    load_passes=0
    for node in networks:
        packed=pack(node,64,2)
        audit=audit_packing(node,packed)
        ca0=child_edge_audit(node,packed,0)
        ca1=child_edge_audit(node,packed,1)
        packet_passes += int(audit['packet_bound_met'])
        load_passes += int(audit['group_load_bound_met'])
        node_max=max(ca0['max_child_edges'], ca1['max_child_edges'])
        maximum_child=max(maximum_child,node_max)
        maximum_child_degree=max(maximum_child_degree,
                                 max((len(v.ports) for v in node.left+node.right),default=0))
        all_shrink &= ca0['paper_shrinkage_satisfied'] and ca1['paper_shrinkage_satisfied']
        edge_conservation &= ca0['exact_port_conservation'] and ca1['exact_port_conservation']
        packet_count += len(packed.packets)
        # On t odd, only coordinate 0 is active for experimental u=1.
        # beta and interpolation point do not change these child edge counts.
        loads=ca0['edges_by_group']
        occupied={label[0] for label in packed.groups_left+packed.groups_right}
        candidate_child_count += 64
        active_child_count += len(occupied)
        group_zero_edges += sum(loads[g] == 0 for g in occupied)
        child_wire_total += sum(loads[g] for g in occupied)
        nodes.append({'parent_wires':node.edges,'child_max':node_max,
                      'coord0_child_max':ca0['max_child_edges'],
                      'coord1_child_max':ca1['max_child_edges'],
                      'packets':len(packed.packets),
                      'packet_bound_met':bool(audit['packet_bound_met']),
                      'load_bound_met':bool(audit['group_load_bound_met']),
                      'occupied_groups':len(occupied),
                      'nonzero_groups':sum(loads[g]>0 for g in occupied)})
        if expand:
            # Every occupied group is represented, including zero-wire nodes;
            # these are the actual control-flow groups in evaluate_deformation.
            for group in sorted(occupied):
                next_networks.append(topology_child(node,packed,group,0))
    peak_python=tracemalloc.get_traced_memory()[1]
    tracemalloc.stop()
    elapsed=time.perf_counter()-tick
    return ({
        'depth':level,'input_nodes':len(networks),
        'parent_wires_total':sum(n.edges for n in networks),
        'parent_wires_max':max((n.edges for n in networks),default=0),
        'max_parent_degree':maximum_child_degree,
        'largest_child_wires':maximum_child,
        'max_child_to_parent_ratio':round(max((n['child_max']/n['parent_wires'] if n['parent_wires'] else 0)
                                         for n in nodes),6) if nodes else 0,
        'packet_count_total':packet_count,
        'packet_bound_passes':packet_passes,'group_load_passes':load_passes,
        'wire_conservation_all':edge_conservation,
        'shrinkage_bound_all':all_shrink,
        'potential_groups':candidate_child_count,
        'executor_occupied_groups':active_child_count,
        'executor_zero_wire_groups':group_zero_edges,
        'child_wire_total_coordinate0':child_wire_total,
        'packing_seconds':round(elapsed,6),
        'peak_python_allocation_bytes':peak_python,
    },next_networks)


def precision_budget(root_wires: int, child_wires: int, extension_degree: int):
    """Arithmetic counts for the a=2,u=1 jet schedule, NOT allocations."""
    base_p=root_wires+3
    q0=3*root_wires
    p1=base_p+120*root_wires  # odd t, h=3M, L=4, a=2
    q1=3*child_wires
    p2=p1+120*child_wires
    first_dense_bytes=extension_degree*q0*((p1+7)//8)
    second_dense_bytes=extension_degree*q0*q1*((p2+7)//8)
    return {'experimental_schedule':'a=2,u=1,L=4',
            'base_precision_bits':base_p,'first_precision_bits':p1,
            'second_precision_bits':p2,
            'first_jet_length':q0,'second_jet_length':q1,
            'first_jet_ring_coordinates':extension_degree*q0,
            'nested_jet_ring_coordinates':extension_degree*q0*q1,
            'first_jet_dense_storage_bytes':first_dense_bytes,
            'nested_jet_dense_storage_bytes':second_dense_bytes,
            'note':'Dense coefficient storage projection, not observed allocation or an intrinsic memory lower bound: a sparse representation could avoid storing most coefficients'}


def geometry_one(family,span,depth=2):
    net=parity_network(family,span)
    expected,rank=independent_count(family,span)
    check_topology_against_real_child(net)
    # Actual geometry of root and *all* 64 subcalls at depth one; do not
    # enumerate 64^2 grandchildren unless explicitly requested.
    levels=[]
    root_packing=pack(net,64,2)
    root_prec=net.edges+3+120*net.edges
    projected_modes=mode_catalog_projection(net,root_packing,root_prec)
    networks=[net]
    for level in range(depth):
        data, children=summarize_level(level,networks,expand=level+1<depth)
        levels.append(data)
        networks=children
    e=max(5, 4*(net.edges-1).bit_length())
    return {'family':family,'span':span,'wires':net.edges,
            'vertices':len(net.left)+len(net.right),'max_degree':max(len(v.ports) for v in net.left+net.right),
            'independent_rank':rank,
            'independent_count':str(expected),
            'independent_count_log2':expected.bit_length()-1 if expected else None,
            'level_audits':levels,
            'root_mode_projection':projected_modes,
            'precision_projection':precision_budget(net.edges,levels[0]['largest_child_wires'],e),
            'full_contraction_run':False}


class TimedContractor(ContractionEngine):
    """Time the original recursive function without altering its arithmetic.

    Inclusive time counts each invocation's children; exclusive time subtracts
    child time. The accounting is deliberately instance-local.
    """
    def __init__(self, config):
        super().__init__(config)
        self.level_seconds_inclusive=defaultdict(float)
        self.level_seconds_exclusive=defaultdict(float)
        self._call_frames=[]

    def contract(self,net,precision=None,depth=0,ring=None):
        t0=time.perf_counter()
        self._call_frames.append([depth,0.0])
        try:
            return super().contract(net,precision=precision,depth=depth,ring=ring)
        finally:
            elapsed=time.perf_counter()-t0
            recorded_depth,child_time=self._call_frames.pop()
            assert recorded_depth==depth
            self.level_seconds_inclusive[depth]+=elapsed
            self.level_seconds_exclusive[depth]+=max(0.0,elapsed-child_time)
            if self._call_frames:
                self._call_frames[-1][1]+=elapsed


def worker(family,span,depth=1):
    from non_exponential_sudoku.core.algebra import _native_ring
    net=parity_network(family,span)
    expected,_=independent_count(family,span)
    start=time.perf_counter()
    solver=TimedContractor(ContractorConfig(net.edges,net.edges+3,
        schedule='geometry64', micro_active_depth=depth,
        leaf=LeafConfig(limit=24,strategy='eliminate'),
        recovery=RecoveryConfig(method='jet',max_jet_coordinates=150000),
        mode=ModeConfig(max_modes=1000,max_tuples=2000)))
    status='success';observed=None;err=None
    try:
        outcome=solver.contract(net)
        observed=outcome[0]
        if outcome[1:] != (0,)*(len(outcome)-1):
            status='noninteger_output'
        if observed != expected: status='wrong_count'
    except (CapacityError,MemoryError) as ex:
        status='capacity_refusal';err=str(ex)[:300]
    except Exception as ex:
        status='exception';err=type(ex).__name__+': '+str(ex)[:300]
    return {'family':family,'span':span,'wires':net.edges,
            'expected':str(expected),'observed':str(observed) if observed is not None else None,
            'status':status,'error':err,'seconds':round(time.perf_counter()-start,6),
            'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'native_ring':_native_ring is not None,
            'active_depth':depth,'contractor_stats':vars(solver.stats),
            'depth_seconds_inclusive':dict(solver.level_seconds_inclusive),
            'depth_seconds_exclusive':dict(solver.level_seconds_exclusive)}


def guarded_worker(family,span,depth=1,timeout=4):
    cmd=[sys.executable,str(Path(__file__).resolve()),'--worker',family,str(span),'--depth',str(depth)]
    def preexec():
        if hasattr(resource,'RLIMIT_AS'):
            resource.setrlimit(resource.RLIMIT_AS,(1280*1024*1024,1280*1024*1024))
    try:
        completed=subprocess.run(cmd,cwd=str(Path(__file__).resolve().parent),
                                 capture_output=True,text=True,timeout=timeout,
                                 preexec_fn=preexec)
        if completed.returncode:
            return {'family':family,'span':span,'active_depth':depth,
                    'status':'process_error','exit_code':completed.returncode,
                    'stderr':completed.stderr[-500:]}
        return json.loads(completed.stdout)
    except subprocess.TimeoutExpired:
        return {'family':family,'span':span,'active_depth':depth,
                'status':'walltime_budget','limit_seconds':timeout}


def main():
    results=[]
    # Sizes increase geometrically, terminating while one pack remains fast.
    # Degree-2 and degree-3 have distinct network families and known counts.
    for family,spans in [
        ('cycle2',[1,2,4,8,16,32,64,128,256,512,1024]),
        ('ladder3',[1,2,4,8,16,32,64,128,256,512,1024]),
        ('pair2',[1,2,4,8,12,16,24]),
    ]:
        for span in spans:
            record=geometry_one(family,span,depth=2)
            results.append(record)
            print(f"geometry {family}:{span} M={record['wires']} "
                  f"child0={record['level_audits'][0]['largest_child_wires']} "
                  f"child1={record['level_audits'][1]['largest_child_wires']}",flush=True)
    # Run full algebra on increasingly larger instances, with independent
    # time/RSS caps; genuine 64-group recursive attempts are included even
    # when the result is a bounded refusal rather than an exact count.
    empirical=[]
    for family,spans in [('cycle2',[1,2,3,4]),('ladder3',[1,2,3,4]),
                         ('pair2',[1,2,4,8,12,16,24])]:
        for span in spans:
            observed=guarded_worker(family,span,depth=1,timeout=(10 if family=='pair2' and span>=24 else 4))
            empirical.append(observed)
            print('execute',family,span,observed['status'],flush=True)
    for family in ('cycle2','ladder3'):
        observed=guarded_worker(family,1,depth=2,timeout=5)
        empirical.append(observed)
        print('2-level',family,observed['status'],flush=True)
    report={
        'title':'Recursive geometry and execution scaling on independently countable bounded-degree networks',
        'version':'v9',
        'methodology':{'r':64,'a':2,'u':1,
           'input_families':'Connected parity-cycle (degree 2), cyclic-ladder (degree 3), and disjoint parity-pair (degree 2) factor graphs',
           'independent_oracle':'Bitpacked GF(2) Gaussian elimination on constraint-incidence matrix',
           'child_topology':'Exact make_child incidence, independently checked against make_child; packet values never evaluated in structural audit',
           'two_levels':'Root and all occupied coordinate-0 child groups; level 2 grandchildren are counted but not instantiated',
           'worker_budget':'4 seconds per connected instance, 10 seconds for largest separated pair, 5 seconds at depth two; 1280MiB address-space limit',
           'scope':'Experimental a=2,u=1 geometry and jets, NOT literal theorem schedule',
           'limits':'Topological child shrinkage alone does not bound mode tuples, precision, memory, or total recursive time'},
        'machine':{'platform':platform.platform(),'python':platform.python_version(),'cpu_count_host':os.cpu_count(),
                   'cpu_affinity':len(os.sched_getaffinity(0)) if hasattr(os,'sched_getaffinity') else None},
        'geometry':results,'execution':empirical,
        'claims':{
           'identity_tested':'Small exact execution outputs compared to independent GF(2) counts',
           'recursive_implementation_tested':'Explicit 64-group child construction and separate topology equivalence checks; multilevel execution only if complete and correct',
           'subexponential_bound_demonstrated':False,
        },
    }
    target=Path(__file__).resolve().parent/'benchmark_scaling_v9.json'
    target.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print('saved',target,flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--worker',action='store_true')
    parser.add_argument('family',nargs='?')
    parser.add_argument('span',nargs='?',type=int)
    parser.add_argument('--depth',type=int,default=1)
    args=parser.parse_args()
    if args.worker:
        print(json.dumps(worker(args.family,args.span,args.depth),sort_keys=True))
    else:
        main()
