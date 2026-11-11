# Source-literal attained-signature arithmetic (v0.21.0)

Source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

## Executable stages

- `BucketProgramArithmetic.choiceAddProgram` is now a 70-label `BitProgram`:
  `ite reg0` chooses stack 1 (`W+A`) or stack 0 (`W`), copies accumulator
  stack 2 into output stack 3 through scratch stack 7, copies the chosen
  offset into work stack 5, resets carry register 0, and runs the actual
  source `BinaryPrograms.Add.littleEndianProgram` on stacks `[3,5,6]`.
  All input stacks remain unchanged; scratch stacks 4–8 return empty.
- `BucketProgramDot.dotStep` reads one serialized coefficient from stack 9,
  consumes one Boolean assignment from 10, runs the actual conditional add,
  clears both temporary coefficient and previous accumulator, then transfers
  the binary sum through stack 11 into 2 without reversing bit order.
- `BucketProgramRow.rowCommand` scans all framed coefficients with the actual
  EOF guard and maintains the numeric sum, including the initial value `1`.
- `BucketProgramNormalize.canonicalRowCommand` executes that row loop then
  calls the source 20-label normalizer for positive integer words.
- `AttainedSignatureProgram.program` is now assembled with the **actual**
  finite canonical row machine. Its matrix and assignment input are preserved;
  its output is a sequence of complete canonical integer-signature records
  in reverse row order. `Rescan.keyCall` can call this real producer.

## Verification and precise limit

The Rust tests use independent numeric arithmetic only **as test oracles**,
not in the executable machine. Cases include exhaustive small additions,
zero and padded words, long carry propagation, row cleanup, canonicalization,
full matrix-to-signature traces, and fail-closed machine budgets. Rust 1.99.1,
offline debug/release and Clippy validation are required before integration.

Not yet complete: `Rescan.candidateProgram`'s predecessor loop and full tuple
DFS/visitor with the actual loader, signed pair accumulation, node finishing,
and differential imported-Lean trace. This implementation is not a proof of
an ETH contradiction or a worst-case runtime bound. Its step counter measures
`BitProgram` source instructions, not primitive machine transitions.

## Input contract

One framed raw coefficient per assignment bit in every row. The output and
work stacks reserved by `ArithmeticCalls.addAt` must be empty at the source
call boundary. This is the same contract the upstream Lean evaluation theorems
use, not an implicit runtime validation of malformed serialized matrices.
EOF-driven loops may consume malformed data but make no semantic correctness
claim on such inputs.
