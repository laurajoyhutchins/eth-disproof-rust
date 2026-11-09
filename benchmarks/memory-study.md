# Peak-memory study (explicit opt-in)

Run locally on **Linux**, from the repository root:

```bash
python -m pip install -e '.[test]'
python -m benchmarks.memory_study --repeats 3 --output artifacts/memory-study.json
```

Or push the exact branch under `verify/memory-*` to execute the separate
`Memory study` workflow, which uploads machine-readable evidence. This is
intentionally not part of the per-commit checkpoint or scheduled native suite.

Each labeled sample runs in a **fresh process**, prepares its fixture first,
then executes exactly one instrumented operation. Every sample must agree
with an independent or closed-form exact result; errors and capacity refusals
fail the study without being treated as a zero-memory observation.

| Case | Exact workload | Independent check |
| --- | --- | --- |
| `leaf.lookup` | Compiled 8-wire Boolean leaf, lookup indices | Exhaustive 256-assignment sum |
| `leaf.indexed` | Same network, positional indices only | Same exhaustive sum |
| `mode.grid3` | Sparse exact mode DP over a 3x3 grid | Closed-form equality count of 2 |
| `nested.jet` | Two Taylor layers over a 2-adic ring | Integer binomial coefficients of `(1+z)^43` |
| `recursive.nested` | Two active recursive levels | Known exact count of 4 |
| `recursive.nested.cap64k` | Same recursion, 64 KiB shared cache budget | Same exact count of 4 |

The worker records Linux `ru_maxrss` (KiB converted to bytes), observed
`VmRSS` before/after the operation, the `tracemalloc` current/peak Python
allocations, elapsed time, and solver's own accounting counters. Be precise
about **what these cannot show**:

- `ru_maxrss` is a process high-water mark, including imports, fixtures,
  native memory, allocator behavior, and Python runtime. Its difference from
  baseline is not a causal measurement of algorithm allocation; zero growth
  does not mean zero allocation.
- `tracemalloc` measures tracked Python allocations, not all allocations
  made by Cython, FLINT or the native allocator. It changes runtime and may
  affect the peak. The peak minus starting trace is an observation, not an
  exact total allocation count.
- The mode/leaf/cache estimates track specific structures with distinct
  scopes. They cannot be added or substituted for total RSS.
- Cross-run comparison requires the same interpreter, build, architecture,
  process settings and representative workload. The report includes source
  identity and every raw sample; no time/RSS regression gate is inferred.

The study is **evidence gathering**, not a new global memory allocator,
asymptotic claim, or non-exponential worst-case proof. Compare RSS and traced
peaks across repeated runs and confirm a material memory hotspot before
changing a production resource policy.
