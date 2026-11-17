# Source-defined head support (additive Rust increment)

Pinned formalization: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

The source `LeafHeadSetupProgram.support` consists of two paid stages, in order:

1. `trueCount = stage PackingHeadProgramPrepareCount.program countRegs [(651,0)] [(1,652)]` with three registers mapped to 13–15. Its exact six-label machine consumes every bit of the selector word at 651 and produces one unary `true` per input bit on 652.
2. `scatterSupport = stage HeadScatterProgram.program scatterRegs [(650,10),(652,11),(128,12)] [(0,670)]` with eight registers mapped to 8–15. The full 8×13 source program reads encoded unary selected-head IDs from 650, the just-produced unary count from 652, and the ambient width from 128; its output on 670 is the ambient head-support mask.

Both stages use the *same* physical 340-based work-bank clearing, input copying, register reset, program lifting, output copying, and finish cleanup already used by the native bootstrap. They do not call the host to splice arrays or count bits. They preserve input ports 650, 651, and 128 and clear temporary 659 and all 13 used workspace ports.

## Verification

`tests/native_head_support.rs` independently exercises the canonicalizer for all 32 bit seeds up to 15 bits; source-label count; nested stage register and stack maps; hundreds of support masks with repeated indices; dirty temporary/output/work ports; unrelated protected masters; and low-budget refusal. For clean workspaces and outputs, the fully compiled `support_program` consumes exactly

```
36*k + 16*I + 29*n + sum(30*j + 55 for j in selected_ids) + 206
```

instructions, where `k` is the number of selected IDs, `I` is the length of their source-encoded record list, and `n` is the ambient coordinate count. This includes the compiled final halt. Pre-existing content on output 652 or 670, or the work bank/temporary, adds two instructions per cleared bit. That formula is checked against the *actual* finite instruction interpreter, not approximated host arithmetic.

This increment is one concrete piece of `prepareHead` and does not implement `heads`, `factors`, `LayoutMatrixProgram.program`, or the complete signature-head loader. It does not claim a Lean-executed differential comparison, source theorem checking, TM2 step refinement, or an ETH complexity result. The real Lean test remains gated on a successful import using the pinned Lean 4.34.1/Mathlib cache.
