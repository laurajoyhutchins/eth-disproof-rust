# Integer cache: native finite-program progress (v0.10.0)

Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

The 8×24 cache program has three source-defined phases:

1. `copies`: `20→17`, `21→18`, `22→19`, using scratch port 3.
2. `flat`: the **unported** `LayoutProgramScalar.hFlatProgram`, which computes every coefficient from the runtime unary `A` and `R` and normalizes to the runtime common width; it must be a compiled finite machine, not a semantic oracle.
3. `makePower`: `21→23`, one pop, then a lifted 2×2 unary exponent machine at registers `[6,7]` and stacks `[23,2]`, constructing the little-endian `2^(R-1)` denominator.

The port implements phases 1 and 3 as directly runnable programs, plus the exact 13-label binary adder, its 17-label linked little-endian program, shifted-plus-prior H-cache cell, framed H-row initializer and 8×19 lifted initial build call. The source bit tables, registers, stack ABI, and original nested halts are preserved.

Acceptance checks: exhaustively test small unsigned operands and dirty/noncanonical words, carry, step counts, width-zero and exponent-zero cases, framed record counts, saved high-row state, scratch cleanup, and non-target stack preservation. `cargo test --offline`, release tests, format and strict Clippy run locally.

**Not executable yet:** the full cache initialization, its full 16×768 staged call, `SignatureHeadLoader.bootstrapProgram`, and the node/leaf query path. No imported-source Lean trace was run. The cached Mathlib environment must be fully restored to claim Lean/Rust differential refinement.

Next precise dependency order: `LayoutProgramScalar.cachePass/cacheProgram` → `LayoutProgramScalar.buildProgram` → `LayoutBinomialProgram.finalFlatten` (including width normalization) → `LayoutProgramScalar.hFlatProgram` → 8×24 `IntegerCache.program` → 16×768 stage and `bootstrapNode` → real node loop.
