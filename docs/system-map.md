# Solver architecture, evidence, and proof boundaries

This is the integration map for the exact-counting work. It describes **one repository with multiple exact algorithms**, not a single proven non-exponential solver. The source of truth for detailed proofs is [claims](claims.md), [bit complexity](bit-complexity.md), [paper admissibility](paper-admissibility.md), and [ETH constructions](eth.md).

## Three different questions

| Question | What counts as evidence | What it does *not* establish |
| --- | --- | --- |
| Is the count right? | Exact reference identities, differential tests, independent counters and witnesses | A runtime bound |
| Can we execute it economically? | Source-pinned timing, process RSS, allocation traces, factor scope and bit-size instrumentation | An asymptotic worst-case theorem |
| Is the algorithm non-exponential? | A complete, non-refusing bit-operation recurrence on a specified growing input family | Correctness or speed on selected instances alone |

No worst-case subexponential algorithm for generalized Sudoku has been established in this repository. A capacity refusal is not an answer, and a bound on recursive **calls**, factor rows, or single arithmetic operations is not a bound on total **bit operations**.

## Implementation boundaries

### 1. Inputs and mathematical meaning

- `sudoku/` owns candidate obligations, board state, direct encodings, frontier counting, decomposition, symmetry, and decision-diagram variants.
- `eth/cnf.py` owns declared-variable Boolean counting semantics. Free variables and auxiliary-variable extensions are explicitly accounted for in reductions.
- `core/` owns exact finite coefficient rings and network objects. `eth/polynomial.py` and related modules provide independent exact rational reference arithmetic.
- Independent exponential enumeration and optional Ganak/FLINT oracles are **correctness witnesses**, not the proposed scalable algorithm.

The direct Sudoku tensor network and the separate CNF encoding are different representations with different size parameters. Results derived for one do not silently transfer to the other.

### 2. Exact algorithm families, not interchangeable shortcuts

| Family | Main modules | Legitimate use | Limit |
| --- | --- | --- | --- |
| Frontier, components, separators | `sudoku/frontier.py`, `components.py`, `separators.py` | Exact DP and certified conditional decomposition | Frontier width can grow |
| Symmetry and compressed states | `sudoku/symmetry.py`, `suffix_graph.py`, `weighted_zdd.py`, `hybrid.py` | Exact count-preserving reductions when certified | Compression is instance-dependent |
| Recursive tensor contraction | `contraction/`, `elimination/`, `recovery/` | Execute the proposed contraction and check admitted instances | Paper schedule, leaf refusals, full bit recurrence unresolved |
| Constructed CNF / ETH experiments | `eth/construction.py`, `factorized_taylor.py`, `interpolation.py` | Exact auxiliary designs, certified measurements, Taylor factor elimination and readout | Dense interactions may produce exponential factors |

The ETH branch was integrated by [PR #7](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/7). Its implicit spectral operator and exceptional projector avoid explicitly constructing large *virtual* objects; this does not automatically bound restricted measurement rank. Factorized Taylor elimination evaluates sparse chain families efficiently, but its cost depends on induced interaction width. The original tuple evaluator remains the default and correctness reference until a general cutover is justified.

### 3. Runtime policies and accelerators

- Resource limits are explicit, configurable and fail closed. Refusal and unsupported configurations remain distinct from exact zero.
- Cached plans, packet values and valuation structures share explicit estimated retention budgets where configured. These are not process-RSS guarantees.
- Python remains the mathematical reference. Optional FLINT/Cython backends should become defaults only where exact differential tests and **paired, source-pinned performance evidence** establish equivalence and improvement; otherwise retain the Python fallback.
- Do not infer asymptotic improvement from eliminated string conversions, cache hits, or a faster native implementation.

### 4. Evidence retained by the repository

- `benchmarks/unified_cost.py` and [unified cost methodology](../benchmarks/unified-cost.md): isolated, paired complete-contraction samples; measured time, RSS, Python-traced memory, logical cost ledger and explicit unknowns.
- `benchmarks/memory_study.py` and [memory methodology](../benchmarks/memory-study.md): independent process observations, including the interpreter baseline.
- `scripts/native_cutover_report.py` and native-cutover workflow: exact-equivalence-first measurements of Cython candidates.
- `benchmarks/eth/` and [ETH experiments](eth.md): implicit operator, projectors, algebraic readout, sparse Taylor factorization with independent count checks.
- `reference/` plus `tests/unit/`: executable conditional bounds for mode reachability, factor support, packet-oracle work, arithmetic, and counting identities.

Each report should keep `measured`, `analytical`, and `unknown` concepts separate. Exact small fixtures are not a growing-family scaling study. Native allocations may be invisible to `tracemalloc`.

## The outstanding theorem, as a dependency chain

1. **Specify the input family and size:** the direct Sudoku encoding has `M = Theta(N log N)` edges for `N` cells, so subexponential in edges alone does not prove subexponential in cells. See [paper admissibility](paper-admissibility.md).
2. **Prove non-refusal and packing:** the literal paper schedule is inactive at practical parameters, and the default direct-leaf budget refuses even a blank 4x4 puzzle. A family-level success theorem is missing.
3. **Close all per-step costs:** include original and inherited oracle evaluation, packet preparation, sparse elimination and hashing, coefficient sizes, rational recovery, modulus setup and memory allocation.
4. **Compose the bit-operation recurrence:** existing local mode, factor-support, oracle-frontier and finite-ring lemmas must combine without an uncapped cost or unproved premise.
5. **Measure growing adversarial families:** collect correct exact counts, refusals, factor scope, coefficient bits, recursion, time and RSS. Measurements can falsify implausible hypotheses but do not replace item 4.

The opt-in research acceptance test for a complete worst-case bit-operation recurrence remains intentionally unresolved. Do not change it to green by weakening its assertion.

## Reproduce at appropriate cost

```bash
python -m pip install -e '.[test]'
python -m pytest -q -m checkpoint
python -m pytest -q -m integration
PYTHONPATH=src:. python -m benchmarks.eth.factorized_taylor_probe
```

Optional native correctness and cost experiments are separate on purpose:

```bash
python -m pip install -e '.[test,native,flint-oracle,sat-oracle,math-audit]'
python build_native.py
python scripts/verify.py checkpoint --require-backend flint --require-backend ganak --require-backend native
python -m benchmarks.unified_cost --cases parity-2wire sudoku-4wire nested-2wire --variants reference plans --repeats 3 --output artifacts/unified-cost.json
```

These commands specify *reproduction procedures*, not a claim that each was rerun on this integration commit.

## How the existing pull requests fit together

| Concern | Integrated PRs | What was retained |
| --- | --- | --- |
| Structural correctness / lightweight checkpoint | [#1](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/1), [#2](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/2), [#3](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/3) | Structured identities, native ring representation, exact CI contracts |
| Honest proof obligations | [#4](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/4), [#6](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/6), [#9](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/9), [#12](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/12), [#13](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/13), [#15](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/15) | Fail-closed theorem test, packet/mode/factor/oracle and nested-ring partial bounds |
| Resource and execution policy | [#5](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/5), [#8](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/8), [#10](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/10), [#11](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/11), [#16](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/16) | Configurable budgets, compiled structures, coordinated caches, adversarial correctness repairs |
| Measurement and cutover evidence | [#14](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/14), [#17](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/17), [#18](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/18) | Paired native performance, isolated memory study, unified cost evidence |
| CNF research / sparse Taylor | [#7](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/7) | Implicit auxiliary/projector, factorized exact Taylor contraction, modular/origin readout experiments |

The PRs are integrated history, not a backlog. The missing item is a *mathematical composition and demonstrated total algorithm*, not another layer of CI or orchestration.
