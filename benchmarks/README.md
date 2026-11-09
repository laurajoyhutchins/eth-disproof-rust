# Reproducible local benchmarks (Linux)

**Canonical entry point:**

```bash
python -m pip install '.[benchmark]'
python scripts/benchmark.py
```

The driver **rebuilds Cython** with `python build_native.py` and verifies that the
compiled `native_ring` is importable before running any measurements. It then:

1. Runs canonical independent correctness checks under pytest, writing `junit.xml`.
2. Runs **pytest-benchmark** in pedantic mode with explicitly configured warmup,
   per-round fresh engine setup, and garbage collection disabled. Native
   `--benchmark-json` output, including raw samples, is saved **unchanged** as
   `timing.json`.
3. Starts a **fresh subprocess for each case/repetition**. Each worker executes
   exactly one contraction and reads Linux `RUSAGE_SELF.ru_maxrss` after it.
   Linux returns KiB, which the worker converts to bytes. Writes `memory.json`.
4. Writes versioned `environment.json`, including git/source identity, compiler,
   CPU, kernel, dependencies, native build outcome, run settings and stage status.

Artifacts are written under `benchmark-results/` by default. The case IDs
`parity-cycle-1`, `parity-cycle-3`, `sudoku-4wire`, `sudoku-8wire`, and
`crossing-4wire` are shared across JUnit properties, pytest-benchmark native
`extra_info`, memory records, and environment metadata.

```bash
python scripts/benchmark.py --rounds 10 --warmup-rounds 3 --memory-repeats 5
python scripts/benchmark.py --cases parity-cycle-1 sudoku-4wire --output /tmp/bench-results
```

The runner exits **nonzero** if any stage fails, any measured count is wrong,
`pytest-benchmark` is unavailable, or an artifact is absent. If the timing plugin
cannot be installed, `--skip-timing` permits a **partial diagnostic** correctness
and memory run; its status remains incomplete, never successful. No fake timing
JSON is produced.

## Measurement semantics

| Metric | Unit | Measurement |
| --- | --- | --- |
| `benchmark.duration` | `s` | Native pytest-benchmark wall-clock samples; setup/validation excluded |
| `benchmark.memory.peak` | `By` | Peak RSS of the **entire fresh worker process** (including interpreter/imports/native), `getrusage(RUSAGE_SELF)` |
| `benchmark.operations` | `{operation}` | Each timing sample invokes one contraction; each RSS worker executes one operation |

These names are local conventions, *not* official OpenTelemetry semantic
conventions. `metrics.json` versions the precise definitions. No OpenTelemetry
SDK or collector is required. Memray is never active for baseline RSS runs.

RSS is a process high-water mark, not memory allocated by the solver nor a
process-tree aggregate. A large import baseline can make distinct cases report
identical peaks. Timing and RSS are separate executions and **must not** be
combined as though they were measured simultaneously.

## Correctness, failure and comparison policy

Only timing and memory observations preceded by a successful correctness gate
are eligible for comparison. Failed workers are retained with `status=failed`,
not assigned a zero or missing-as-success value. Missing native timing JSON is
an incomplete run. Timeouts and import failures are explicit failures.

The harness does **not** impose automatic timing or RSS regression thresholds.
Compare equivalent versions on the same hardware, kernel, Python, extension
build flags, input cases, and harness settings. Use distributions (sample median,
variance, outliers, and sample size), not a single-time threshold; compare peak
RSS across several independent workers. Declare any future regression threshold
and comparison method in a separately versioned policy before gating CI.

The timing plugin is a declared optional dependency, not vendored into this
repository. Install it from your trusted package index before expecting
`timing.json`.

## Benchmark families and shared plumbing

The canonical contraction runner (`scripts/benchmark.py`) and the exact-cover
variant study (`scripts/native_dlx_study.py`) share evidence mechanics in
`benchmarks/harness.py`: subprocess execution, Git/source metadata, JUnit
counts, and validation of **unchanged native pytest-benchmark JSON**. Neither
runner imports the other. Each retains its own cases, reference oracles,
benchmark settings, and fresh-process RSS worker.

The instrumented growth study (`python -m benchmarks.growth_study`) and the
recursive profiler (`scripts/recursive_measure.py`) remain separate: their
structural counters, capacity-refusal handling, profiling overhead, and hard
worker timeout contracts differ from native wall-clock benchmark results.
These are not interchangeable performance measurements.

`pytest-benchmark` is required for a completed native timing run. The canonical
runner's `--skip-timing` mode intentionally exits nonzero with incomplete status,
even if correctness and RSS measurements pass.
