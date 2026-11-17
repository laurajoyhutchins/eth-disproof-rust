# Source-derived H flat cache and integer cache (v0.12.0)

Pinned source: [`openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).

The Rust implementation `native_flatten.rs` completes the **finite BitProgram implementation** of `LayoutProgram.IntegerCache.program`, including its `hFlatProgram` dependency. This supersedes the partial-status description in `docs/h-cache-iteration-v0.11.0.md` without changing previous test fixtures.

## Exact finite-program boundary

| Lean source | Rust constructor | Contract |
|---|---|---|
| `ModularPrograms.paddingProgram` | `padding_program()` | Five labels: pop unary shape, pop input or zero, push reversed output |
| `ModularRingPrograms.normalizeProgram` | `normalize_program()` | Exactly 12 linked labels (5 padding + 3 clear + 4 transfer), no extra wrapper labels |
| `LayoutBinomialProgram.normalizeComponent` | `normalize_component_command()` | Paid width copy, lifted normalize, paid transfer into reverse buffer |
| `LayoutBinomialProgram.flatRow` | `flat_row_command()` | Real framed pair parser, positive and negative normalization, loop controlled by parsed tag |
| `LayoutBinomialProgram.flatProgram` | `flat_program()` | Real `flatRow` followed by physical transfers of both reverse accumulators |
| `LayoutBinomialProgram.finalFlatten` | `final_flatten_command()` | Fixed lift into 8×20 machine, width port 18→19 |
| `LayoutProgramScalar.hFlatProgram` | `h_flat_program()` | Source H-cache builder followed by the signed-component flatten call |
| `LayoutProgram.IntegerCache.program` | `integer_cache_program()` | Preserving copies of 20/21/22 to 17/18/19, lifted H flat program, paid denominator generation |

All code dimensions are fixed: the input parameters `A`, `R`, and `width` appear only as unary Boolean stack lengths. The Rust constructors make no host-number calls to calculate coefficients, serialize records, or normalize their values. `Program::run` enforces source instruction and stack-bit limits.

The source precondition for the mathematical H-cache contract is `1 + 2*A*R <= width`. A narrower width physically truncates the word because `padTo` truncates; it must not be presented as a correct exact H value. The library exposes the low-level finite program without silently inventing or repairing admission conditions.

## Tests

`tests/native_flatten.rs` covers the exact 5-/12-label programs, normalization at widths 0..7 and longer inputs, existing-buffer preservation, signed positive and negative records, physical ordering, H-cache iterations for a range of `(A,R)`, complete integer-cache stacks and retained inputs, and failure on an insufficient step budget. The expected coefficient values are checked by an independent reference recurrence in the tests, not extracted from the program's output.

## Unproven boundary

The tests compare Rust semantics with the *definitions* in pinned Lean source, **not with imported-source Lean execution**. A complete original Lean runtime and Mathlib import cache are still required for a differential run. No claim is made for `SignatureHeadLoader.bootstrapProgram`, the remaining node loop, pair traversal, query reconstruction, the outer SAT program, a primitive TM2 refinement, or an ETH theorem.
