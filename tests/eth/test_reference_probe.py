"""The reference probe must not advertise unavailable paper-path metrics."""
import pytest

from benchmarks.eth.reference_probe import probe
from non_exponential_sudoku.eth import CNFFormula

pytestmark = pytest.mark.checkpoint


def test_reference_probe_records_exact_counts_and_missing_paper_costs() -> None:
    result = probe(CNFFormula(3, ((1, 2), (-1, 3))))
    assert result['count'] == 4
    assert result['algorithm_status'] == 'exhaustive_reference_only'
    assert result['boolean_assignments'] == 8
    assert result['max_coefficient_bits'] >= 1
    assert result['wall_seconds'] >= 0
    assert result['peak_process_rss_bytes'] is None or result['peak_process_rss_bytes'] > 0
    for field in ('taylor_pairs', 'measurement_tuples', 'group_assignments', 'estimated_bit_operations'):
        assert result[field] is None
