from __future__ import annotations

from typing import TYPE_CHECKING, Protocol
from .statistics import Counters
from .cost_ledger import charge, charge_peak

if TYPE_CHECKING:
    from ..elimination.factors import Factor

class GrowthProbe(Protocol):
    def retained(self, budget: ModeBudget, factors: list[Factor]) -> None: ...
    def temporary(self, budget: ModeBudget, states: int, terms: int, description: str) -> None: ...

class CapacityError(RuntimeError):
    """An explicit resource refusal. Never silently changes algorithms."""

class ModeBudget:
    """Per-invocation resource budget; nested contractors get independent instances.

    Counts work and bounds live factors, temporary coefficients, and ordering.
    Budget counters are distinct from aggregate observability statistics.
    """
    def __init__(self, *, stats: Counters, error: type[Exception] = CapacityError,
                 max_states: int = 4096, max_terms: int = 100000,
                 max_operations: int = 2000000, max_children: int = 50000,
                 max_bytes: int = 128*1024*1024,
                 bytes_per_coefficient: int = 256) -> None:
        self.stats=stats
        self.CapacityError=error
        self.max_states=max_states
        self.max_terms=max_terms
        self.max_operations=max_operations
        self.max_children=max_children
        self.max_bytes=max_bytes
        self.bytes_per_coefficient=bytes_per_coefficient
        self.operations=0
        self.order_scans=0
        self.children=0
        self.factors: list[Factor] = []
        self.growth_probe=getattr(stats, "growth_probe", None)

    def charge_child(self) -> None:
        self.children+=1
        charge("mode_child_factor_evaluations")
        if self.children>self.max_children:
            raise self.CapacityError('Mode DP child-contraction limit')
        self.stats.mode_dp_local_child_evaluations+=1

    def work(self,n: int = 1) -> None:
        self.operations+=n
        charge("mode_dp_work_units",n)
        self.stats.mode_dp_operations+=n
        if self.operations+self.order_scans>self.max_operations:
            raise self.CapacityError('Mode DP arithmetic work limit')

    def order_work(self,n: int) -> None:
        self.order_scans+=n
        charge("mode_dp_order_scans",n)
        self.stats.mode_dp_order_scans=getattr(self.stats,'mode_dp_order_scans',0)+n
        if self.order_scans+self.operations>self.max_operations:
            raise self.CapacityError('Mode DP elimination-order work limit')

    def guard_states(self,states: int,description: str) -> None:
        if states>self.max_states:
            raise self.CapacityError(
                f'Mode DP factor size limit ({description}: {states} > {self.max_states})')

    def guard_live(self) -> None:
        states=sum(len(f.table) for f in self.factors)
        terms=sum(sum(len(p) for p in f.table.values()) for f in self.factors)
        self.stats.mode_dp_peak_factor_states=max(self.stats.mode_dp_peak_factor_states,states)
        self.stats.mode_dp_peak_polynomial_terms=max(self.stats.mode_dp_peak_polynomial_terms,terms)
        estimated=terms*self.bytes_per_coefficient + 128*states
        charge_peak("mode_live_factor_rows",states)
        charge_peak("mode_live_polynomial_terms",terms)
        charge_peak("mode_live_estimated_bytes",estimated)
        self.stats.mode_dp_peak_estimated_bytes=max(self.stats.mode_dp_peak_estimated_bytes,estimated)
        if self.growth_probe is not None:
            self.growth_probe.retained(self,self.factors)
        if terms>self.max_terms:
            raise self.CapacityError(f'Mode DP retained coefficient limit: {terms} > {self.max_terms}')
        if estimated>self.max_bytes:
            raise self.CapacityError(f'Mode DP estimated memory limit: {estimated} > {self.max_bytes}')

    def guard_build(self, states: int, terms: int, description: str) -> None:
        # Enforced during factor construction, not only after materializing
        # what might otherwise be a multi-GB temporary table.
        if self.growth_probe is not None:
            self.growth_probe.temporary(self,states,terms,description)
        if states>self.max_states:
            raise self.CapacityError(f'Mode DP factor size limit ({description})')
        if terms>self.max_terms:
            raise self.CapacityError(f'Mode DP temporary coefficient limit ({description})')
        if terms*self.bytes_per_coefficient+128*states>self.max_bytes:
            raise self.CapacityError(f'Mode DP temporary memory limit ({description})')
