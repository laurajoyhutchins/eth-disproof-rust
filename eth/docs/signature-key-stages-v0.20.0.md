# v0.20.0: finite signature-key scanner and canonical word normalization

Source pin: [`openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae).

## Source-defined commands now executable

| Rust routine | Lean source | Exact machine / ports |
| --- | --- | --- |
| `trim_program` | `SubexpParameterProgram.trimProgram` | 3 registers × 3 stacks, 6 labels |
| `prepare_log_program` | `SubexpParameterProgram.prepareLogProgram` | Linked transfer+trim, 10 labels |
| `counter_normalize_program` | `CounterNormalizeProgram.program` | Reset, prepare, restore; 20 labels |
| `canonical_row_normalize_call` | `BucketProgramNormalize.normalizeCall` | 8×12; registers `[0,1,2]`, stacks `[2,3,4]` |
| `signature_step` | `BucketProgramSignature.signatureStep` | 8×15, one framed row |
| `signature_command` / `signature_program` | `BucketProgramSignature.signatureCommand` | 8×15, read/while/emit |
| `attained_signature_command` / `attained_signature_program` | `AttainedSignatureProgram.command` | 8×16, preserve original row matrix on stack 15 |
| `rescan_key_call` | `AttainedSignatureProgram.Rescan.keyCall` | 16×24 identity-mapped leaf ABI |

**Important `Fin` distinction:** the source's `Fin.castAdd` and `Fin.castLE` extend
an upper bound **without changing the numeric index**. They are not offsets.
In particular `rowCallPorts = Fin.castAdd 3`, `signaturePorts = Fin.castAdd 1`,
`signatureRegisters = Fin.castAdd 8`, and `signatureStacks = Fin.castAdd 8`
are identity embeddings on their respective indices. The 8×12 row call
therefore uses stacks 0..11, not 3..14.

The outer scanner's read-word operation is the original parser followed by
physical reversing transfer. Its frame emitter is the source transfer,
false delimiter, and `TupleProgram.escapeProgram` call, charged at `8n+8`
source instructions per emitted n-bit row. The original serialized matrix is
copied and preserved by `AttainedSignatureProgram.command`.

The normalizer is a fixed 20-label program. For positive inputs only, it
returns the value in the minimal little-endian width `log2(value)+1`, clears
both work stacks and all three registers, and honors the source's
`9*input_length+21` bound including final halt. Zero is **not** claimed to
have a value-preserving normalization contract.

## Verification

Unit tests use the genuine finite-machine instructions, not a host-language
arithmetic evaluator. They independently check positive numeric values,
padded input lengths, register/stack frames, raw framed-record decoding,
output order, and instruction-capacity refusal.

The outer scanner's callback is deliberately a **test-only** finite command
that writes a constant key or a row-presence bit. This tests the *outer*
source syntax and framed visit order. It is **not** `canonicalRowProgram` and
its keys are not actual signatures. The production constructors accept a
`Program<8,12>` parameter and do **not** provide or silently substitute a
fake default for the missing inner machine.

## Remaining steps

1. Port `BucketProgramArithmetic.choiceAddProgram` and its word-addition
   dependencies, then the `BucketProgramDot.rowCommand`.
2. Compose `BucketProgramNormalize.canonicalRowCommand` using the normalizer
   from this increment, yielding the source's real `canonicalRowProgram`.
3. Supply that real program to the outer scanner, then wire
   `Rescan.prepareKey`, `Rescan.body`, and `Rescan.candidateProgram` on 16×24,
   and lift through `SignatureTupleNative.candidateMachine` on 40×896.
4. Run imported Lean/Rust differential traces after full Mathlib restoration.

This increment does not establish a complete predecessor predicate, complete
signed query, nor a worst-case subexponential bit-complexity result.
