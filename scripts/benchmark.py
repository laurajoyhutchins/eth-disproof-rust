#!/usr/bin/env python3
"""Run exact correctness, native pytest-benchmark timing and Linux peak-RSS trials.

Artifacts: junit.xml, timing.json (native plugin schema), memory.json, environment.json.
A missing plugin or failed measurement is *never* recorded as successful.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import sysconfig
import uuid

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / 'src')]
from benchmarks.cases import CASE_IDS, prepare_case
from benchmarks.harness import (THREAD_VARIABLES, iso_now, command_output, version_of,
    source_hash_files, git_metadata, cpu_model, junit_counts, run_process, validate_native_timing)

HARNESS_VERSION = '1.0.0'

def source_hash():
    paths = sorted((ROOT/'src').rglob('*.py')) + sorted(ROOT.glob('*.pyx'))
    paths += sorted((ROOT/'benchmarks').glob('*.py')) + sorted((ROOT/'scripts').glob('benchmark.py'))
    paths += sorted((ROOT/'tests/benchmark').glob('*.py')) + [ROOT/'tests/fixtures/expected_results.json', ROOT/'pyproject.toml']
    return source_hash_files(paths)


def native_status(env):
    cmd = [sys.executable, '-c',
           'import native_ring; from non_exponential_sudoku.core.algebra import _native_ring; '
           'assert _native_ring is not None; print(native_ring.__file__)']
    result = subprocess.run(cmd, env=env, cwd=ROOT, text=True,
                            capture_output=True, timeout=10)
    return {'ok': result.returncode == 0,
            'module_file': result.stdout.strip() if result.returncode == 0 else None,
            'error': result.stderr.strip()[-2000:] if result.returncode else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'benchmark-results')
    parser.add_argument('--cases', nargs='+', choices=CASE_IDS, default=CASE_IDS)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--warmup-rounds', type=int, default=2)
    parser.add_argument('--memory-repeats', type=int, default=3)
    parser.add_argument('--correctness-timeout', type=float, default=120)
    parser.add_argument('--timing-timeout', type=float, default=300)
    parser.add_argument('--memory-timeout', type=float, default=60)
    parser.add_argument('--skip-timing', action='store_true',
                        help='Partial diagnostic run only; overall run remains incomplete')
    args = parser.parse_args()
    if (min(args.rounds, args.memory_repeats) < 1 or args.warmup_rounds < 1 or
        min(args.correctness_timeout, args.timing_timeout, args.memory_timeout) <= 0 or
        len(set(args.cases)) != len(args.cases)):
        parser.error('Rounds/repeats/timeouts must be positive, cases unique, warmup >= 1')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    for name in ('junit.xml', 'timing.json', 'memory.json', 'environment.json'):
        (output/name).unlink(missing_ok=True)
    env = os.environ.copy()
    env['PYTHONPATH'] = os.pathsep.join(filter(None, [str(ROOT), str(ROOT/'src'),env.get('PYTHONPATH','')]))
    env['SUDOKU_BENCH_CASES'] = ','.join(args.cases)
    env['SUDOKU_BENCH_ROUNDS'] = str(args.rounds)
    env['SUDOKU_BENCH_WARMUP'] = str(args.warmup_rounds)
    environment = {
        'schema_version': '1.0.0',
        'harness_version': HARNESS_VERSION,
        'run_id': str(uuid.uuid4()),
        'started_at_utc': iso_now(),
        'status': 'incomplete',
        'git': git_metadata(),
        'source_sha256': source_hash(),
        'python': {'version': platform.python_version(), 'implementation': platform.python_implementation(),
                   'executable': sys.executable},
        'cython_version': version_of('Cython'),
        'pytest_version': version_of('pytest'),
        'pytest_benchmark_version': version_of('pytest-benchmark'),
        'compiler': {'cc': os.environ.get('CC') or sysconfig.get_config_var('CC'),
                     'version': (command_output(['cc', '--version']) or '').splitlines()[:1],
                     'python_cflags': sysconfig.get_config_var('CFLAGS'),
                     'build_cflags': os.environ.get('CFLAGS'),
                     'build_ldflags': os.environ.get('LDFLAGS')},
        'system': {'kernel': platform.release(), 'system': platform.system(),
                   'machine': platform.machine(), 'cpu_model': cpu_model(),
                   'logical_cpu_count': os.cpu_count()},
        'environment_variables': {key: env.get(key) for key in THREAD_VARIABLES},
        'configuration': {
            'cases': {case_id: prepare_case(case_id).parameters for case_id in args.cases},
            'timing': {'rounds': args.rounds, 'iterations_per_round': 1,
                       'warmup_rounds': args.warmup_rounds,
                       'garbage_collection': 'disabled',
                       'sequential': True, 'timed_setup': False, 'timed_validation': False,
                       'unit': 's', 'engine': 'pytest-benchmark',
                       'raw_samples': 'native pytest-benchmark JSON with --benchmark-save-data'},
            'memory': {'repetitions': args.memory_repeats, 'per_run_process': 'fresh subprocess',
                       'ru_maxrss_scope': 'RUSAGE_SELF', 'linux_ru_maxrss_unit': 'KiB',
                       'output_unit': 'By', 'instrumented_with_memray': False,
                       'memory_timeout_seconds': args.memory_timeout},
        },
        'metric_definition': 'benchmarks/metrics.json',
        'stages': {},
    }
    def save_env():
        environment['ended_at_utc'] = iso_now()
        (output/'environment.json').write_text(json.dumps(environment, indent=2, sort_keys=True)+'\n')
    try:
        # The benchmark contract requires rebuilding native arithmetic, not
        # relying on whatever Cython binary happened to be present.
        build = run_process([sys.executable,'build_native.py'], env, 120,
                            output/'native-build.log')
        build['native_import'] = native_status(env) if build['exit_code'] == 0 else None
        environment['stages']['native_build'] = build
        if build['exit_code'] or not build['native_import']['ok']:
            environment['status'] = 'failed_native_build'
            return 1

        correct = run_process([sys.executable,'-m','pytest','-q',
                               'tests/benchmark/test_correctness.py', '-o', 'junit_family=xunit2',
                               f'--junitxml={output/"junit.xml"}'],env,
                              args.correctness_timeout, output/'correctness.log')
        counts = junit_counts(output/'junit.xml')
        correct['junit_counts'] = counts
        correct['passed'] = (correct['exit_code'] == 0 and not correct['timed_out']
                             and counts is not None and counts['tests'] == len(args.cases)
                             and counts['failures'] == counts['errors'] == counts['skipped'] == 0)
        environment['stages']['correctness'] = correct
        if not correct['passed']:
            environment['status'] = 'failed_correctness'
            return 1

        if args.skip_timing:
            timing = {'status': 'skipped_by_user', 'success': False}
        elif importlib.util.find_spec('pytest_benchmark') is None:
            timing = {'status': 'missing_dependency', 'success': False,
                      'error': 'Install the [benchmark] extra: pip install -e .[benchmark]'}
        else:
            timing = run_process([
                sys.executable,'-m','pytest','-q','tests/benchmark/test_timing.py',
                '--benchmark-disable-gc', '--benchmark-save-data',
                f'--benchmark-json={output/"timing.json"}',
            ],env,args.timing_timeout,output/'timing.log')
            verified, error = validate_native_timing(
                output/'timing.json', ((case,) for case in args.cases),
                ('benchmark.case',), args.rounds)
            timing['status'] = ('complete' if timing['exit_code'] == 0 and verified
                                else 'failed')
            timing['success'] = timing['status'] == 'complete'
            if error:
                timing['validation_error'] = error
        environment['stages']['timing'] = timing

        memory_rows = []
        for case in args.cases:
            for repetition in range(args.memory_repeats):
                result = run_process([
                    sys.executable, '-m','benchmarks.memory_worker','--case',case,
                ], env, args.memory_timeout)
                row = {'case_id': case, 'repetition': repetition + 1,
                       'status': 'failed', 'exit_code': result['exit_code']}
                if result['exit_code'] == 0:
                    # The worker has exactly one JSON record on stdout. Repeat
                    # with subprocess.run so stdout is available for validation.
                    # See subprocess helper below, which preserves the output.
                    try:
                        data = json.loads(result['stdout'].strip())
                        if (data['verified'] is True and data['case_id'] == case and
                            isinstance(data['metric']['value'], int) and data['metric']['value'] > 0):
                            row = {**data, 'repetition': repetition + 1, 'status': 'verified'}
                        else:
                            row['error'] = 'Invalid/mismatched worker measurement'
                    except (ValueError, KeyError, TypeError) as err:
                        row['error'] = 'Malformed worker JSON: ' + str(err)
                else:
                    row['error'] = result['error']
                memory_rows.append(row)
        mem_success = len(memory_rows) == len(args.cases) * args.memory_repeats and all(
            row['status'] == 'verified' for row in memory_rows)
        (output/'memory.json').write_text(json.dumps({
            'schema_version': '1.0.0', 'run_id': environment['run_id'],
            'unit': 'By', 'metric_name': 'benchmark.memory.peak',
            'instrument': 'gauge', 'measurement_scope': 'fresh Linux process/RUSAGE_SELF',
            'status': 'complete' if mem_success else 'failed',
            'results': memory_rows,
        },indent=2,sort_keys=True)+'\n')
        environment['stages']['memory'] = {'success': mem_success,
            'passed': sum(row['status'] == 'verified' for row in memory_rows),
            'total': len(memory_rows)}
        environment['status'] = ('complete' if mem_success and timing['success']
                                 else 'incomplete_or_failed')
        return 0 if environment['status'] == 'complete' else 1
    finally:
        save_env()
        print('Benchmark status:', environment['status'], 'artifacts:', output, flush=True)


if __name__ == '__main__':
    sys.exit(main())
