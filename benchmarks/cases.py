"""Canonical executable benchmark cases. Setup and count verification are not timed.

Each operation closes over a prepared immutable network and a fresh contraction
engine. The same operation factory is used by correctness, timing and RSS runs.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Callable
import json

from non_exponential_sudoku import (
    ContractionEngine, ContractorConfig, LeafConfig, ModeConfig,
    ModeLimits, Padic, RecoveryConfig, simple_network,
)
from non_exponential_sudoku.core.packing import pack
from non_exponential_sudoku.core.modes import mode_catalog

ROOT = Path(__file__).resolve().parents[1]
FIXTURE_LEDGER = json.loads((ROOT / 'tests/fixtures/expected_results.json').read_text())
SUDOKU = {case['id']: case for case in FIXTURE_LEDGER['cases']['SUDOKU_CASES']}
PARITY = {case['id']: case for case in FIXTURE_LEDGER['cases']['PARITY_CASES']}
CASE_IDS = ('parity-cycle-1', 'parity-cycle-3', 'sudoku-4wire', 'sudoku-8wire', 'crossing-4wire')


def selected_case_ids():
    import os
    selection = os.environ.get('SUDOKU_BENCH_CASES')
    if not selection:
        return CASE_IDS
    choices = tuple(selection.split(','))
    if not choices or len(set(choices)) != len(choices) or any(c not in CASE_IDS for c in choices):
        raise ValueError('Invalid SUDOKU_BENCH_CASES selection')
    return choices


@dataclass(frozen=True)
class PreparedCase:
    case_id: str
    expected: int
    parameters: dict
    independent_oracle: str
    new_operation: Callable[[], Callable[[], int]]

    def validate(self) -> int:
        actual = self.new_operation()()
        if actual != self.expected:
            raise AssertionError(f'{self.case_id}: expected {self.expected}, got {actual}')
        return actual


def prepare_case(case_id: str) -> PreparedCase:
    if case_id not in CASE_IDS:
        raise ValueError(f'Unknown benchmark case {case_id!r}')

    if case_id.startswith('parity-'):
        from reference.scaling_experiment import parity_network, independent_count
        span = int(case_id.rsplit('-', 1)[-1])
        net = parity_network('cycle2', span)
        expected = PARITY[f'cycle2-{span}']['expected']
        independent, _ = independent_count('cycle2', span)
        if independent != expected:
            raise AssertionError('GF(2) reference disagrees with canonical ledger')
        config = ContractorConfig(
            net.edges, net.edges + 3, schedule='micro',
            leaf=LeafConfig(strategy='eliminate'),
            recovery=RecoveryConfig(method='jet', streaming=True),
            mode=ModeConfig(strategy='eliminate', factorization='components', join='adaptive'),
        )
        return PreparedCase(case_id, expected,
            {'family': 'cycle2', 'span': span, 'edges': net.edges, 'schedule': 'micro'},
            'independent-GF2-rank',
            lambda: (lambda engine=ContractionEngine(config): engine.contract(net)[0]),
        )

    if case_id.startswith('sudoku-'):
        from reference.real_sudoku_bench import puzzles, independent_count_sparse
        from reference.local_support import pin_band_wires
        target = ('9x9-77-givens-two-solutions' if case_id == 'sudoku-4wire'
                  else '9x9-73-givens-four-solutions')
        _, puzzle, declared = next(row for row in puzzles() if row[0] == target)
        expected = SUDOKU[target]['expected']
        independent = independent_count_sparse(puzzle, 12)
        if declared != expected or independent != expected:
            raise AssertionError('Independent Sudoku count disagrees with canonical ledger')
        net, _ = pin_band_wires(puzzle)
        config = ContractorConfig(
            net.edges, net.edges + 3, schedule='micro',
            leaf=LeafConfig(strategy='eliminate'),
            recovery=RecoveryConfig(method='jet', streaming=True),
            mode=ModeConfig(strategy='eliminate', factorization='components', join='adaptive'),
        )
        return PreparedCase(case_id, expected,
            {'puzzle_id': target, 'active_wires': net.edges, 'schedule': 'micro'},
            'independent-Sudoku-search',
            lambda: (lambda engine=ContractionEngine(config): engine.contract(net)[0]),
        )

    # Four free binary wires: the reference is 2**4, not the implementation's mode sum.
    size = 4
    net = simple_network(
        size,
        [([i], {(0,): 1, (1,): 1}) for i in range(size)],
        [([i], {(0,): 1, (1,): 1}) for i in range(size)],
    )
    packing = pack(net, 64, 2,
        (tuple((0, 0) for _ in range(size)),
         tuple((1, 0) for _ in range(size))))
    precision = 9
    config = ContractorConfig(
        size, precision, schedule='geometry64',
        leaf=LeafConfig(strategy='eliminate'),
        mode=ModeConfig(strategy='eliminate', factorization='components',
                        order='min_fill', join='adaptive'),
        limits=ModeLimits(max_factor_states=20000, max_operations=5_000_000),
    )
    def fresh_operation():
        engine = ContractionEngine(config)
        ring = Padic(engine.e, engine.f, precision)
        modes = mode_catalog(net, packing, 1, precision)
        return lambda: engine.evaluate_deformation(
            net, packing, modes, 1, ring.basis(3), ring, 0)[0]
    return PreparedCase(case_id, 1 << size,
        {'wires': size, 'group_count': 64, 'precision': precision,
         'coordinate': 0, 'schedule': 'geometry64'},
        'independent-binary-assignment-count', fresh_operation)
