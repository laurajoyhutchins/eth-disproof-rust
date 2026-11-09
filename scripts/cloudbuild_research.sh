#!/usr/bin/env bash
# Non-required Cloud Build research and benchmark suites.
# Execute exactly one allowlisted suite on an immutable admitted source.
set -euo pipefail

suite="$1"
case "$suite" in
  cnf-scaling|sudoku-scaling|sudoku-representation|unified-cost|valuation-scaling|memory|native-cutover) ;;
  *) echo "unknown research suite: $suite" >&2; exit 2 ;;
esac

case "$suite" in
  native-cutover)
    python -m pip install --disable-pip-version-check -e '.[native,test,benchmark]'
    python build_native.py --force
    python -m pytest -q tests/contracts/test_native_kernel_differential.py tests/contracts/test_sparse_native_jet_arithmetic.py tests/integration/test_recursive_optimized.py tests/unit/test_native_cutover_report.py
    mkdir -p artifacts
    SUDOKU_BENCH_PAIRS='sparse-grid3:python,sparse-grid3:cython,sparse-grid4:python,sparse-grid4:cython,dense-grid3:python,dense-grid3:cython' SUDOKU_BENCHMARK_ROUNDS=7 \
      python -m pytest -q tests/benchmark/test_native_dlx_timing.py --benchmark-only --benchmark-save-data --benchmark-json=artifacts/native-sparse-timing.json
    SUDOKU_RECURSIVE_PAIRS='parity-2wire:reference,parity-2wire:packet,parity-2wire:leaf,sudoku-4wire:reference,sudoku-4wire:packet,sudoku-4wire:leaf,sudoku-8wire:reference,sudoku-8wire:packet,sudoku-8wire:leaf,nested-2wire:reference,nested-2wire:packet,nested-2wire:leaf,crossing-4wire:reference,crossing-4wire:packet,crossing-4wire:leaf,parity-2wire:plans,parity-2wire:leaf-plans,sudoku-4wire:plans,sudoku-4wire:leaf-plans,sudoku-8wire:plans,sudoku-8wire:leaf-plans,nested-2wire:plans,nested-2wire:leaf-plans,crossing-4wire:plans,crossing-4wire:leaf-plans' SUDOKU_BENCHMARK_ROUNDS=7 \
      python -m pytest -q tests/benchmark/test_recursive_timing.py --benchmark-only --benchmark-save-data --benchmark-json=artifacts/native-recursive-timing.json
    python -m pytest -q tests/benchmark/test_native_ring_timing.py --benchmark-only --benchmark-save-data --benchmark-json=artifacts/native-ring-timing.json
    python scripts/native_cutover_report.py artifacts/native-sparse-timing.json artifacts/native-recursive-timing.json artifacts/native-ring-timing.json --output artifacts/native-cutover-report.json
    ;;
  cnf-scaling)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m pytest -q tests/benchmark/test_cnf_scaling.py -m checkpoint
    python -m pytest -q tests/benchmark/test_cnf_scaling.py -m integration
    python -m benchmarks.eth.cnf_scaling --families path matching clique --sizes 2 4 6 --summations tuples eliminate fused multilinear --repeats 1 --timeout 8 --threshold 64 --r 2 --Q 2 --R 2 --output artifacts/cnf-scaling.json
    python -m pytest -q tests/eth/test_unfolding_rank.py -m checkpoint
    python -m pytest -q tests/eth/test_unfolding_rank.py -m integration
    python -m benchmarks.eth.unfolding_rank --max-pairs 4 --output artifacts/eth-unfolding-rank.json
    python -m pytest -q tests/eth/test_support_rank.py -m checkpoint
    python -m pytest -q tests/eth/test_support_rank.py -m integration
    python -m pytest -q tests/eth/test_spectral_rank_growth.py
    python -m benchmarks.eth.spectral_rank_growth --families path matching xor_pairs clique --sizes 3 4 5 6 --max-exact-n 6 --max-profile-n 6 --output artifacts/eth-spectral-rank-growth.json
    python -m pytest -q tests/eth/test_paper_admitted_witness.py -m checkpoint
    python -m pytest -q tests/eth/test_paper_admitted_witness.py -m integration
    python -m benchmarks.eth.paper_admitted_witness --lambda-bits 17179869184 --finite-n 4096 --output artifacts/eth-paper-admission.json
    ;;
  sudoku-scaling)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m pytest -q tests/benchmark/test_sudoku_scaling.py
    python -m benchmarks.sudoku_scaling --cases 4x4-empty 4x4-8-givens-four-solutions 9x9-73-givens-four-solutions 9x9-hard-unique 16x16-252-givens-two-solutions 16x16-248-givens-eight-holes --algorithms frontier paper --repeats 3 --timeout 30 --output artifacts/sudoku-scaling.json
    ;;
  sudoku-representation)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m pytest -q tests/unit/test_sudoku_representation_rank.py -m integration
    python -m benchmarks.sudoku_representation_audit --boxes 2 3 4 --packing --output artifacts/sudoku-representation.json
    ;;
  unified-cost)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m pytest -q tests/benchmark/test_unified_cost.py
    python -m benchmarks.unified_cost --cases parity-2wire sudoku-4wire nested-2wire --variants reference plans --repeats 3 --timeout 60 --output artifacts/unified-cost.json
    ;;
  valuation-scaling)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m benchmarks.valuation_scaling --repeats 2 --timeout 40 --memory-mib 768 --output artifacts/valuation-scaling.json
    set +e
    python -m benchmarks.valuation_scaling --cases recursive-L4-dense-p5 --repeats 1 --timeout 40 --memory-mib 768 --output artifacts/valuation-dense-refusal.json
    status=$?
    set -e
    if [[ "$status" -ne 0 && "$status" -ne 2 ]]; then exit "$status"; fi
    python - <<'PYCODE'
import json
from pathlib import Path
data = json.loads(Path('artifacts/valuation-dense-refusal.json').read_text())
pairs = data['comparisons']
assert len(pairs) == 1
samples = pairs[0]['original_samples'] + pairs[0]['pruned_samples']
assert len(samples) == 2
assert all(s['status'] in ('capacity_refused', 'verified') for s in samples)
assert all(s['actual'] == s['expected'] for s in samples if s['status'] == 'verified')
print('Dense stress arms:', [s['status'] for s in samples])
PYCODE
    ;;
  memory)
    python -m pip install --disable-pip-version-check -e '.[test]'
    python -m benchmarks.memory_study --repeats 3 --timeout 45 --output artifacts/memory-study.json
    ;;
esac
python - "$suite" <<'PYCODE'
import hashlib
import sys
from pathlib import Path
files = sorted(p for p in Path('artifacts').rglob('*') if p.is_file())
if not files:
    raise SystemExit('research suite produced no retained artifact')
for p in files:
    print(sys.argv[1] + '_evidence_sha256', hashlib.sha256(p.read_bytes()).hexdigest(), p)
PYCODE
