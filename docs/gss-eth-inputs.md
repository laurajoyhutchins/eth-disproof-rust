# GSS puzzles as ETH counting inputs

This is a **source-of-instances** path, not an alternative Sudoku solver or a claim that the proposed ETH algorithm runs on arbitrary CNF. The actual Rust input seam is `lean_eth_reference::parse_dimacs` and the existing `eth-frontend` binary.

## Convert and inspect

From the repository root:

```sh
# Small native Generic Sudoku Solver puzzle, with exactly two solutions.
python3 tools/gss_to_dimacs.py eth/fixtures/gss/latin_2x2.gss -o /tmp/latin_2x2.cnf

# Read the formula through the original-source Rust physical frontend.
# A successful result is `status=frontend-completed`, NOT a #SAT count.
cargo run --locked --offline -p lean-eth-reference --bin eth-frontend -- \
  --max-steps 20000000 --max-stack-bits 300000 < /tmp/latin_2x2.cnf

# Separate, explicitly exponential semantic reference oracle: expected count=2.
cargo run --locked --offline -p lean-eth-reference --bin lean-eth-reference \
  < /tmp/latin_2x2.cnf
```

The input has four cells with two digits, and row/column-style pairs declared as custom GSS blocks. Independent enumeration of the 16 possible four-cell grids establishes exactly two completions. The DIMACS uses eight variables and 24 clauses. `eth/tests/gss_sat_input.rs` checks the same count through the Rust ingestion parser and its bounded reference solver. This is a **test of the adapter and count semantics**, not of the proposed subexponential counter.

## Scaling the input topology

An empty 4×4 standard Sudoku, with rows, columns, and 2×2 boxes, is at `eth/fixtures/gss/empty_4x4.gss`. Generate both direct CNF and width-3 CNF:

```sh
python3 tools/gss_to_dimacs.py eth/fixtures/gss/empty_4x4.gss -o /tmp/empty_4x4.cnf
python3 tools/dimacs_to_3cnf.py /tmp/empty_4x4.cnf -o /tmp/empty_4x4.3cnf
```

The converter deterministically emits **64 variables and 448 clauses** for direct CNF. The definitional reduction yields **128 variables and 640 clauses**, with each clause of width at most three. These are input-size measurements, not ETH machine performance results. The bounded semantic reference leaf refuses such instances because its limit is 20 variables; refusal is expected and must not be presented as a failure to parse the input or a successful proposed-algorithm run.


**The signed-CSR recognizer is not a general Sudoku solver.** That independent certificate path recognizes a narrowly specified three-literal recurrence family. Even a Sudoku instance reduced to clauses of width at most three is not automatically admitted by that recognizer. The general source-defined query/high/leaf/DFS pipeline remains unfinished.

To try a larger 9×9 puzzle, place its native GSS text in a file and run the same commands. The frontend may refuse on its step/stack budgets. Preserve the DIMACS source, optional transformed output, exact revision, limits, elapsed time, physical instruction count, and peak live stack bits if a run finishes. Rejections should be recorded with the specific refusal reason. Do not infer primitive-machine bounds or asymptotic complexity from these measurements.

## Why the three-clause conversion retains #SAT

Ordinary satisfiability-preserving clause splitting can introduce multiple witnesses. `tools/dimacs_to_3cnf.py` instead uses *definitional* OR-prefix variables. For a clause `(a ∨ b ∨ c ∨ d)`, define `y ↔ (a ∨ b)` with the three clauses

```text
-a y 0
-b y 0
a b -y 0
```

and replace the original clause by `y c d 0`. Each assignment to the **original** variables uniquely determines `y`; the transformed formula is satisfied exactly when the original clause is. For longer clauses the construction recurses on the prefix, creating exactly `length - 3` auxiliary variables, each uniquely determined by the earlier ones. Consequently the ordinary satisfying-assignment count **over all declared output variables** is unchanged. Original variables retain their DIMACS indices; only auxiliaries are appended.

The Python test `tools/test_dimacs_to_3cnf.py` independently enumerates all original assignments and all auxiliary extensions for bounded positive, negative, duplicate, tautological, empty, and multiple-clause cases. This finite test does **not** establish Lean-to-Rust correctness or the ETH time bound. A Lean theorem formalizing the unique-extension property against the exact source CNF semantics is a separate future proof obligation.

## Reproduce bounded checks

```sh
python3 -m unittest discover -s tools -p 'test_gss_to_dimacs.py' -v
python3 -m unittest discover -s tools -p 'test_dimacs_to_3cnf.py' -v
cargo test --locked --offline --all-targets
```

The first two checks are standard-library Python tests. The Rust gate is part of the repository's existing acceptance procedure. Run in the actual checkout with the pinned toolchain. **Do not treat an unexecuted CI job or an absent local Rust toolchain as a passing result.**

See [the executable source boundary](eth/docs/m2-runnable-frontend.md), [the repository's ETH evidence](eth/docs/evidence.md), and the [technical notebook's GSS model-bijection study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/gss-sudoku-cnf-encoding.md).
