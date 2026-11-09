# Exact Sudoku and counting experiments

An executable study of exact generalized-Sudoku counting, recursive tensor
contraction, and related #SAT constructions. **No worst-case subexponential
algorithm for generalized Sudoku has been proved here.** An exact count is a
correctness result for a supported input, not a running-time theorem.

## The objects

| Object | Code | Mathematical role |
| --- | --- | --- |
| `Puzzle` / `CNFFormula` | `sudoku/three_cnf.py`, `eth/cnf.py` | Input and count semantics |
| `Padic`, jets and `Network` | `core/` | Exact coefficient rings and tensor graphs |
| `ContractionEngine` | `contraction/`, `elimination/`, `recovery/` | Recursive contraction, modes and coefficient recovery |
| Candidate obligations | `sudoku/state.py` | Shared row/column/box exact-cover representation |
| Frontier counters | `sudoku/frontier.py`, `sudoku/components.py`, `sudoku/separators.py` | Exact dynamic programming and conditional factorization |
| Symmetry counters | `sudoku/symmetry.py`, `sudoku/suffix_graph.py` | Certified finite-group and hypergraph reductions |
| Decision diagrams | `sudoku/weighted_zdd.py`, `sudoku/hybrid.py` | Exact weighted state-map compression |
| ETH reference | `eth/` | CNF reductions, separation, interpolation and explicit admission |

The modules implement **distinct algorithms** with distinct resource models;
there is no claim that they are interchangeable solvers or collectively imply
a subexponential bound.

See the [solver architecture and evidence map](docs/system-map.md) for the
integrated algorithm families, reproducible experiments, PR lineage, and
remaining proof obligations.

## Reproduce the claims

```bash
python -m pip install -e '.[test]'
python -m pytest -q -m checkpoint    # Pure Python; optional backends may skip
python -m pytest -q -m integration   # Slower cross-component comparisons
```

Optional independent backends are intentionally separate:

```bash
python -m pip install -e '.[test,native,flint-oracle,sat-oracle,math-audit]'
python build_native.py
python scripts/verify.py checkpoint --require-backend flint --require-backend ganak --require-backend native
```

For the mathematical arguments see [Sudoku state algebra](docs/sudoku.md),
[CNF and interpolation](docs/eth.md), [recursive contraction](docs/mathematics.md),
and [open proof obligations](docs/claims.md). Run `git log --reverse --format='%h %s'`
to read the repository in conceptual order. Commits were **constructed from the
finished source tree** to make dependencies explainable, not to recreate the
chronology of experimentation.

**Licensing:** no redistribution license has been selected. See [licensing](docs/licensing.md).
