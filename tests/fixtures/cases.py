"""Typed accessors for the sole machine-readable fixture ledger."""
from dataclasses import dataclass
from pathlib import Path
import json


@dataclass(frozen=True)
class CountCase:
    id: str
    kind: str
    expected: int
    parameter: int
    oracle: str


_records = json.loads(Path(__file__).with_name('expected_results.json').read_text())
PARITY_CASES = tuple(CountCase(**case) for case in _records['cases']['PARITY_CASES'])
SUDOKU_CASES = tuple(CountCase(**case) for case in _records['cases']['SUDOKU_CASES'])
