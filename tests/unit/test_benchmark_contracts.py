"""No benchmark plugin needed to verify evidence parsing and metric definitions."""
import json
from pathlib import Path
import pytest
from benchmarks.cases import CASE_IDS, selected_case_ids
from benchmarks.harness import junit_counts, validate_native_timing, source_hash_files

pytestmark = pytest.mark.checkpoint
ROOT = Path(__file__).resolve().parents[2]


def test_case_ids_are_stable_unique():
    assert len(CASE_IDS) == len(set(CASE_IDS))
    assert all(case and ' ' not in case for case in CASE_IDS)


def test_selection_rejects_invalid_cases(monkeypatch):
    monkeypatch.setenv('SUDOKU_BENCH_CASES', 'not-a-case')
    with pytest.raises(ValueError):
        selected_case_ids()
    monkeypatch.setenv('SUDOKU_BENCH_CASES', 'parity-cycle-1,parity-cycle-1')
    with pytest.raises(ValueError):
        selected_case_ids()


def test_metric_unit_contracts():
    definitions = json.loads((ROOT/'benchmarks/metrics.json').read_text())
    assert definitions['metrics']['benchmark.duration']['unit'] == 's'
    assert definitions['metrics']['benchmark.memory.peak']['unit'] == 'By'
    assert definitions['metrics']['benchmark.operations']['unit'] == '{operation}'


def test_failed_or_malformed_junit_is_not_passed(tmp_path):
    path = tmp_path/'junit.xml'
    assert junit_counts(path) is None
    path.write_text('<testsuite')
    assert junit_counts(path) is None
    path.write_text('<testsuite tests="1" failures="1" errors="0" skipped="0"/>')
    assert junit_counts(path)['failures'] == 1


def test_native_timing_requires_complete_finite_samples(tmp_path):
    path = tmp_path / 'timing.json'
    expected = [('case-a', 'reference'), ('case-a', 'native')]
    def row(variant, samples):
        return {'extra_info': {'benchmark.case': 'case-a', 'benchmark.variant': variant},
                'stats': {'data': samples}}
    valid = [row('reference', [0.1, 0.2, 0.3]), row('native', [0.4, 0.5, 0.6])]
    path.write_text(json.dumps({'benchmarks': valid}))
    assert validate_native_timing(path, expected, ('benchmark.case', 'benchmark.variant'), 3) == (True, None)
    for invalid in (valid[:1], [valid[0], valid[0]],
                    [valid[0], row('native', [0.4, 0.5])],
                    [valid[0], row('native', [0.4, float('nan'), 0.6])],
                    [valid[0], row('native', [0.4, 0, 0.6])]):
        path.write_text(json.dumps({'benchmarks': invalid}))
        accepted, message = validate_native_timing(path, expected,
                                                   ('benchmark.case', 'benchmark.variant'), 3)
        assert not accepted and message


def test_source_hash_includes_relative_paths(tmp_path):
    first = tmp_path / 'first.py'
    second = tmp_path / 'second.py'
    first.write_text('same content')
    second.write_text('same content')
    assert source_hash_files([first], tmp_path) != source_hash_files([second], tmp_path)
    assert source_hash_files([first, second], tmp_path) == source_hash_files([first, second], tmp_path)
