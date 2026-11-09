"""Exact experimental counting components.

This commit history is a constructed dependency exposition, not an
account of implementation chronology."""

from .contraction.engine import ContractionEngine
from .runtime.config import ContractorConfig, ModeConfig, ModeLimits, RecoveryConfig, PacketConfig, LeafConfig, RecursionConfig
from .runtime.budget import CapacityError
from .runtime.cost_ledger import CostLedger
from .runtime.work_trace import WorkTrace
from .core.algebra import Padic, modulus_polynomial
from .core.network import Network, Vertex, simple_network
from .sudoku.encoding import sudoku_network

__all__ = ['ContractionEngine', 'ContractorConfig', 'ModeConfig', 'ModeLimits', 'RecoveryConfig', 'PacketConfig', 'LeafConfig', 'RecursionConfig', 'CapacityError', 'CostLedger', 'WorkTrace', 'Padic', 'modulus_polynomial', 'Network', 'Vertex', 'simple_network', 'sudoku_network']
