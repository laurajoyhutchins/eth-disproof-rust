# Exact CNF: growing-family full-pipeline experiment

This experiment executes the complete `count_cnf_reference` pipeline, not just
the spectral operator, sparse Taylor elimination, or a synthetic contraction.
It intentionally records noncompletion rather than changing the algorithm to
meet a benchmark. It does **not** certify a subexponential-time algorithm.

## Independent count families

| Family | Clauses | Independent exact count |
| --- | --- | --- |
| `path` | `(x_i or x_(i+1))` for adjacent variables | `F_(n+2)` |
| `matching` | Disjoint positive 2-clauses | `3^(n/2)` |
| `xor_pairs` | Disjoint positive and negative 2-clauses per pair | `2^(n/2)` |
| `clique` | `(x_i or x_j)` for every pair | `n+1` |

For matching and XOR families, `n` must be even. The oracle is an independent
closed-form identity and, for `n <= oracle_max_vars`, also independently
checked with the bounded brute-force reference **before measurement**. The
production counting path never uses brute force or Ganak as a fallback.

A path or matching formula can be easy for specialized DP, while the clique
has a dense interaction graph. These families are complementary structural
probes, **not** worst-case hardness proofs.

## Protocol and interpretation

Every scenario runs twice in fresh Linux subprocesses: uninstrumented
(`baseline`) and Python allocation traced (`observed`). Alternate arm
ordering across repeats. Record full-pipeline duration excluding family
construction and independent oracle, process high-water RSS, observed Python
allocation peak, leaf contributions, Taylor pairs, measurement tuples, factor
assignments, factor scope/table peaks, factor eliminations, Hermite operations,
and maximum observed coefficient bit length.

The fixed finite reference parameters `r=2,Q=2,R=2` are **not** the
manuscript's asymptotic parameter schedule. The default experimental
sparsification threshold is `64`, which commonly avoids branching on small
examples. The default `max_leaves=64` is a resource budget, not a
theorem. The report stores them explicitly.

The same formula and reference parameters are evaluated with `tuples`,
`eliminate`, and opt-in `fused`. `eliminate` uses certified group-mask
factors for each finite-difference pair. `fused` first telescopes the
Boolean differences exactly, then contracts factors over original Boolean
variables and truncated polynomial coefficients. Its pair count is zero,
but this says nothing about induced factor width or arithmetic work. All
three must match the independent exact count; neither factorization
establishes the manuscript's non-exponential worst-case algorithm.

**Important:** `factor_scope_peak` counts *groups* for `eliminate`, but
*Boolean variables* for `fused`. The JSON reports `factor_scope_basis` so
width measurements are not compared across incompatible units. A zero `measurement_tuples` value under
elimination does not imply negligible work.

Outcomes:

- `verified`: the entire exact count completed and matched the independent count
- `capacity_refusal`: the solver exhausted a declared budget, count is null
- `timeout`: the worker exceeded the wall limit, count is null
- `discordant_outcomes`: the two arms had different valid completion/refusal/
  timeout outcomes. Preserve both raw samples and report **no paired speed
  ratio** or verified paired completion. This can expose tracing overhead
- `failed`: wrong answer, missing evidence, process error, or malformed arms;
  the entire report fails rather than absorbing the sample into a median

A `complete` report means every requested attempt has an explicit,
classified outcome, including noncomparable pairs. It does **not** mean
every formula was solved or every timing comparison was meaningful.
`all_cases_solved` and `outcome_counts` distinguish those claims.

On refusal or timeout, **no partial factors, coefficient sizes, or leaf counts
are fabricated**. An instrumented allocator trace does not observe native
FLINT allocations. RSS includes Python startup and imports. Neither
operations counted nor timings prove a worst-case asymptotic bound.

## Reproduce

```bash
python -m pip install -e '.[test]'
python -m pytest -q tests/benchmark/test_cnf_scaling.py -m checkpoint
python -m pytest -q tests/benchmark/test_cnf_scaling.py -m integration
python -m benchmarks.eth.cnf_scaling \
  --families path matching clique \
  --sizes 2 4 6 \
  --summations tuples eliminate fused \
  --repeats 1 --timeout 8 \
  --threshold 64 --r 2 --Q 2 --R 2 \
  --output artifacts/cnf-scaling.json
```

The opt-in **CNF full-pipeline scaling** workflow runs the same bounded
experiment on pushes to `verify/cnf-scaling-*` or by manual dispatch. It
preserves raw JSON whether the run passes or fails, but is not a per-commit
latency gate.

Next, use the output to identify the **first** capacity or timing boundary.
Then vary one of: n, structural width, fixed construction parameters, or
sparsification threshold. Never infer a non-exponential claim from successful
small instances or treat explicit finite reference parameters as theorem
admission.
