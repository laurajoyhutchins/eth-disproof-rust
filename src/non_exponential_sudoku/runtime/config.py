"""Immutable, validated settings for the exact contraction engine."""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Literal
from .cache import CachePolicy

if TYPE_CHECKING:
    from ..core.packing import LabelPair

@dataclass(frozen=True)
class ModeConfig:
    strategy: Literal['eliminate','enumerate','packet_eliminate']='eliminate'
    factorization: Literal['components','whole']='components'
    order: Literal['min_fill','min_states']='min_fill'
    join: Literal['adaptive','sparse','enumerate']='adaptive'
    native_sparse: bool=True
    # Optional legacy guard. Catalog allocation is bounded by ModeLimits bytes.
    max_modes: int | None=None
    max_tuples: int=20000

    def __post_init__(self) -> None:
        if self.strategy not in ('eliminate', 'enumerate', 'packet_eliminate'):
            raise ValueError('Invalid mode strategy')
        if self.factorization not in ('components', 'whole'):
            raise ValueError('Invalid factorization')
        if self.order not in ('min_fill', 'min_states'):
            raise ValueError('Invalid mode elimination order')
        if self.join not in ('adaptive', 'sparse', 'enumerate'):
            raise ValueError('Invalid mode join strategy')
        if not isinstance(self.native_sparse, bool):
            raise ValueError('native_sparse must be boolean')
        if ((self.max_modes is not None and self.max_modes <= 0)
                or self.max_tuples <= 0):
            raise ValueError('Mode resource limits must be positive')

@dataclass(frozen=True)
class ModeLimits:
    max_components: int=20000
    max_factor_states: int=4096
    max_live_terms: int=100000
    max_operations: int=2000000
    max_child_contractions: int=50000
    max_estimated_bytes: int=128*1024*1024
    def __post_init__(self) -> None:
        if any(v<=0 for v in vars(self).values()):
            raise ValueError('Mode elimination limits must be positive')

@dataclass(frozen=True)
class RecoveryConfig:
    method: Literal['interpolate','jet']='interpolate'
    streaming: bool=False
    max_jet_coordinates: int=500000

    def __post_init__(self) -> None:
        if self.method not in ('interpolate', 'jet'):
            raise ValueError('Invalid recovery')
        if self.streaming and self.method != 'jet':
            raise ValueError('Streaming Hermite currently requires jet recovery')
        if self.max_jet_coordinates <= 0:
            raise ValueError('Jet coordinate limit must be positive')

@dataclass(frozen=True)
class PacketConfig:
    cache_limit: int|None=None
    node_limit: int=250000
    miss_limit: int=2000000
    checkpoint_coordinates: int=0

    def __post_init__(self) -> None:
        if self.node_limit <= 0 or self.miss_limit <= 0:
            raise ValueError('Packet node and miss limits must be positive')
        if self.cache_limit is not None and self.cache_limit < 0:
            raise ValueError('Packet cache limit must be nonnegative')
        if self.checkpoint_coordinates < 0:
            raise ValueError('Packet checkpoint limit must be nonnegative')
        if self.checkpoint_coordinates and self.cache_limit is None:
            raise ValueError('Packet checkpoints require lazy packet coefficient evaluation')

@dataclass(frozen=True)
class LeafConfig:
    strategy: Literal['enumerate','eliminate']='enumerate'
    limit: int=18
    micro_threshold: int=0
    adaptive_limit: int=0
    # Width and lookup are planning controls; bytes bound live factor tables.
    max_width: int=16
    lookup_entries: int=8192
    max_factor_bytes: int=128*1024*1024

    def __post_init__(self) -> None:
        if self.strategy not in ('enumerate', 'eliminate'):
            raise ValueError('Invalid leaf settings')
        if (self.limit <= 0 or self.micro_threshold < 0 or self.adaptive_limit < 0
                or self.max_width <= 0 or self.lookup_entries < 0
                or self.max_factor_bytes <= 0):
            raise ValueError('Invalid Leaf resource limits')

@dataclass(frozen=True)
class ZeroSupportPolicy:
    """Bounded opt-in proof of zero before an exact child contraction."""

    enabled: bool=False
    pre_factor: bool=False
    max_child_edges: int=16
    max_vertex_arity: int=8
    max_support_rows: int=2048
    max_mode_terms: int=2048

    def __post_init__(self) -> None:
        if type(self.enabled) is not bool:
            raise ValueError('Zero-support enabled must be Boolean')
        if type(self.pre_factor) is not bool or (self.pre_factor and not self.enabled):
            raise ValueError('Pre-factor support requires enabled Boolean policy')
        if any(type(x) is not int or x < 1 for x in (
            self.max_child_edges, self.max_vertex_arity, self.max_support_rows,
            self.max_mode_terms,
        )):
            raise ValueError('Zero-support limits must be positive integers')


@dataclass(frozen=True)
class RecursionConfig:
    """Optional recursion paths for differential testing and bounded acceleration."""
    child_plans: bool=True
    native_packet: bool=False
    native_leaf: bool=False
    packet_memo_entries: int=0
    packet_memo_bytes: int=1024*1024
    prepared_packet_entries: int=0
    prepared_packet_bytes: int=8*1024*1024
    child_cache: CachePolicy=field(default_factory=lambda: CachePolicy(
        max_bytes=8*1024*1024, max_entries=128))
    compiled_plans: CachePolicy=field(default_factory=lambda: CachePolicy(
        max_bytes=8*1024*1024, max_entries=64))
    valuation_structures: CachePolicy=field(default_factory=lambda: CachePolicy(
        max_bytes=8*1024*1024, max_entries=8))
    zero_support: ZeroSupportPolicy=field(default_factory=ZeroSupportPolicy)
    pre_factor_support_cache: CachePolicy=field(default_factory=lambda: CachePolicy(
        max_bytes=1024*1024, max_entries=16))
    # Optional contraction-wide cache retention; does not cap arithmetic RSS.
    shared_cache_bytes: int | None=None

    def __post_init__(self) -> None:
        if any(not isinstance(v,bool) for v in (self.child_plans,self.native_packet,self.native_leaf)):
            raise ValueError('Recursion kernel switches must be boolean')
        if self.packet_memo_entries<0 or self.packet_memo_bytes<1:
            raise ValueError('Invalid bounded packet-entry memoization budget')
        if self.prepared_packet_entries<0 or self.prepared_packet_bytes<1:
            raise ValueError('Invalid prepared packet budget')
        if self.prepared_packet_entries and not self.child_plans:
            raise ValueError('Prepared packet reuse requires compiled child plans')
        if (not isinstance(self.child_cache, CachePolicy)
                or not isinstance(self.compiled_plans, CachePolicy)
                or not isinstance(self.valuation_structures, CachePolicy)):
            raise TypeError('Cache policies must be CachePolicy instances')
        if not isinstance(self.zero_support, ZeroSupportPolicy):
            raise TypeError('Zero-support policy must be ZeroSupportPolicy')
        if not isinstance(self.pre_factor_support_cache, CachePolicy):
            raise TypeError('Pre-factor support cache policy must be CachePolicy')
        if self.shared_cache_bytes is not None and (
            type(self.shared_cache_bytes) is not int or self.shared_cache_bytes < 1
        ):
            raise ValueError('Invalid shared cache budget')

@dataclass(frozen=True)
class ContractorConfig:
    s: int
    precision: int
    schedule: Literal['paper','micro','geometry64']='paper'
    mode: ModeConfig=field(default_factory=ModeConfig)
    limits: ModeLimits=field(default_factory=ModeLimits)
    recovery: RecoveryConfig=field(default_factory=RecoveryConfig)
    packets: PacketConfig=field(default_factory=PacketConfig)
    leaf: LeafConfig=field(default_factory=LeafConfig)
    root_labels: object|None=None
    micro_active_depth: int=1
    recursion: RecursionConfig=field(default_factory=RecursionConfig)

    def __post_init__(self) -> None:
        if self.schedule not in ('paper','micro','geometry64'):
            raise ValueError('Invalid schedule')
        if self.s<1 or self.precision<1:
            raise ValueError('s and precision must be positive')
        if self.mode.strategy=='packet_eliminate' and self.schedule=='paper':
            raise ValueError('Direct packet elimination is not the paper recurrence')
        if self.recovery.method=='jet' and self.schedule not in ('micro','geometry64'):
            raise ValueError('Jet recovery is experimentally supported only in micro/geometry64 schedules')
        if self.recovery.method=='jet' and self.micro_active_depth<1:
            raise ValueError('Jet recursion needs at least one active layer')
        if self.packets.cache_limit is not None and self.recovery.method!='jet':
            raise ValueError('Packet lazy evaluation requires jet recovery')
