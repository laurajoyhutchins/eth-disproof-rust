# Lean ETH Rust port: signed incidence matrix to canonical signature

**Original Lean source:** `openai/math@4eaee87548250b2682affda7d05d947c05554bae`

This increment implements a substantial executable slice, rather than separate
source-helper placeholders. Everything in the production path executes as a
fixed Boolean-stack instruction table, with no host integer arithmetic or
runtime-selected instruction generation.

## Physical program boundaries

| Source program | Rust port | Machine |
|---|---|---|
| `ModularPrograms.subtractProgram`, `paddingProgram` | `native_signed_arithmetic::{subtract,padding}_program` | 8×3, 13/5 labels |
| `ModularPrograms.{subtract,padding}LEProgram` | linked `*_le_program` | 8×3, 17/9 labels |
| `SaturatingSubtractionProgram.command` | `saturating_subtract_program` | 8×8 |
| `ArithmeticCalls.addAt`, `BucketProgram.shiftProgram` | `add_at_command`, `shift_program` | 8×10 |
| `MatrixProgramSupport.readWord`, `emitFrame` | `native_matrix_preprocess` | physical framed stack operations |
| `BucketProgram.preReverseProgram`, `preRowProgram`, `preMatrixProgram` | `native_matrix_preprocess` | 8×4 / 8×14 / 8×17 |
| `SignatureHeadLoader.shiftCommand` | `signature_shift_command` | source stage in 16×768 |
| `SubexpParameterProgram.prepareLogProgram` | `prepare_log_program` | literal 3×3, 10 labels |
| `CounterNormalizeProgram.program` | `normalize_program` | 3×3 |
| `BucketProgram.choiceAddProgram`, `rowProgram`, `canonicalRowProgram` | `native_signature` | 8×9 / 8×12 |
| `BucketProgram.signatureProgram` | `signature_program` | 8×15 |

The **additional** `signed_matrix_signature_program` is an integration adapter,
not a Lean source definition. It composes `preMatrixProgram` with
`signatureProgram` in a single 8×64 physical machine using paid copies and
cleanup, with external ports:

- `0`: binary offset `W`, retained;
- `14`: framed signed matrix, consumed;
- `17`: head assignment, retained;
- `15`: shifted unsigned matrix, retained;
- `18`: framed canonical signature keys, produced.

Both sign components `P` and `N` are little-endian bits in independent escaped
frames. The offset computation performs natural-number subtraction with
saturation (`W - N`), followed by paid addition of `P`. For the integer
interpretation **the source requires `N <= W`** for each coefficient.

For a row of `h` coefficients and head bits `x`, the machine computes the
canonical representation of

`1 + sum_{i=0}^{h-1} (x_i ? (W - N_i + P_i) : W)`.

When `N_i <= W`, this equals `1 + h*W + sum_i x_i*(P_i-N_i)`. The leading one
makes the normalizer total even for zero-valued rows. The serialized key
contains all rows, in the source-defined reverse framed order. Two keys
are equal exactly when every signed row sum is equal, subject to the input
contract. There is no reliance on a Rust `usize` counter in the program itself.

## Verification

Local Rust 1.99.1 (offline) checks:

- Full integration suite in debug and release.
- `cargo fmt --all -- --check`; `cargo clippy --offline --all-targets -- -D warnings`.
- Exhaustive small-width subtraction/padding and frame round trips.
- Exact source instruction counts for the linked arithmetic and frame-reversal
  routines, including the final compiled halt.
- Nested signed matrix processing, conditional addition, normalization,
  retained register/stack boundaries and resource-limit refusal.
- Exhaustive execution of all 64 head assignments in a four-row, six-column
  signed matrix, checking **all 4,096 pairs** for the equivalence:
  `physical_key(x) == physical_key(y)` iff all signed linear row forms agree.
  Maximum observed for this fixture: **47,129** machine instructions and
  **1,233** peak stack bits per assignment.

## What this does *not* establish

The actual `LayoutMatrixProgram.program LayoutFiberSumProgram.command`,
its native `LayoutProgram.EntryBank.command`, and the surrounding
`SignatureHeadLoader.localProgram` are **not** complete. The pipeline currently
starts with a supplied signed incidence matrix, rather than deriving it from
live node/pair/master data. Head preparation and the signed readout therefore
remain separate pieces of the whole native node evaluator.

Imported-source Lean/Rust differential testing requires a working pinned
Lean 4.34.1/Mathlib restoration; Rust self-tests alone cannot replace it.
An end-to-end ETH theorem, polynomial worst-case bit complexity and TM2
resource refinement have **not** been established by this work.
