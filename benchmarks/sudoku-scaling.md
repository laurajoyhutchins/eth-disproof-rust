# Full-input Sudoku scaling: bounded empirical evidence

This study complements `benchmarks/unified_cost.py`, which measures small
recursive tensor fixtures. Every input here is a complete original Sudoku
puzzle's **givens**. It does not secretly condition on a known solution.

Run locally (Linux) with a short verification subset:

```bash
python -m pip install -e '.[test]'
python -m pytest -q tests/benchmark/test_sudoku_scaling.py
python -m benchmarks.sudoku_scaling \
  --cases 4x4-empty 9x9-73-givens-four-solutions 16x16-252-givens-two-solutions \
  --algorithms frontier paper --repeats 1 --timeout 20 \
  --output artifacts/sudoku-scaling.json
```

Run the **Sudoku full-input scaling** workflow manually or push the exact
source commit to a `verify/sudoku-scaling-*` branch. It preserves raw JSON
and never changes the required per-commit checkpoint.

## Inputs and independent oracle

The fixed fixtures include 4x4, 9x9 and 16x16 boards, varying clue counts
and a genuinely empty 4x4 Sudoku (288 completions). A new 16x16 eight-hole
fixture is constructed by erasing digits from a public canonical pattern,
but its count is **not** inferred from the generating pattern. Before calling
either backend, a separate, bounded MRV enumeration computes the count and
checks any fixture-declared expectation. MRV is never used by production
solver code. It is outside the measured solver time and has an explicit
node budget. If MRV refuses, the record is `oracle_refusal`, not verified.

The `frontier` path runs the exact specialized dynamic-programming counter
with a 20,000-state/500,000-transition/32 MiB estimated-state budget.
The `paper` path runs the unchanged paper-schedule contractor, preceded by
the support-preserving conditioning needed to convert givens into a band
network. Its default leaf limit is 18 edges. The paper path may refuse.

These are **different algorithms**: matching input and exact answers permits
a correctness comparison, not an attribution of a speedup to Appendix D.

## Measurement semantics

Each scenario and arm runs in a new process. `baseline` has no optional
CostLedger/WorkTrace/tracemalloc observers; `observed` adds them. Timing
includes conditioning and exact counting from givens, but excludes the
independent reference oracle and fixture construction. Python allocations
exclude native untracked buffers. RSS includes interpreter/import overhead.
The report retains the solver's structural counters and (where available)
the reconciled cost ledger; no call count is presented as bit complexity.

Every attempt is explicitly classified:

- `verified`: completed and agreed with independently determined exact count.
- `capacity_refusal`: resource policy stopped execution; **no count**.
- `timeout`: subprocess did not finish before the configured wall limit;
  **no count**.
- `oracle_refusal`: independent MRV exceeded its own node budget;
  solver correctness **not assessed**.
- `failed`: crash, wrong count, malformed evidence or inconsistent paired arms.

`status=complete` means every scheduled attempt has a recorded outcome,
**not** that every Sudoku instance was solved. Use `all_cases_solved` and
`outcome_counts` to distinguish those claims. In particular, a capacity
refusal never silently becomes a zero solution count.

## Limits of inference

The 4x4/9x9/16x16 examples are a *finite instance experiment*, not a
worst-case scaling limit. Most larger-board fixtures have many givens and
few live choices, so increasing cell count here is not equivalent to
increasing difficulty. A 9x9 hard puzzle supplies an adversarial data point,
not a universal complexity result. The paper schedule's practical activation
problem and the full recursive oracle/bit-cost recurrence remain open.

Next: a parameterized sequence of increasing residual hardness, explicit
per-phase exclusive timing, native operand bit-length measurements, and
statistically controlled repeated runs on pinned hardware. Only after these
are independently validated should an automatic performance threshold be set.
