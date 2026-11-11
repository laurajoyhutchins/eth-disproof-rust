# OpenAI ETH Rust test accuracy audit (2026-11-10)

The Rust tests produce several distinct kinds of evidence, which must not be conflated.

- **Executable instruction behavior:** Native prefix and bit-machine tests check register/stack state, source-instruction counts and bounded refusal. They do **not** establish imported-source Lean/Rust trace equality.
- **Source identity:** `reference/source-manifest.json` now includes Git blob SHAs from the pinned `openai/math@4eaee87548250b2682affda7d05d947c05554bae` revision for **every Lean file named by the 42-stage registry**. The Rust test checks exact path membership and well-formed 40-hex pins. This is a source catalogue, not a byte-for-byte implementation equivalence test.
- **Synthetic composition:** `native_seam_tdd.rs` combines `NativeLayoutLoad.command` directly with `PairNativeSetup.setupCaller`. The actual `QueryStreamProgram.nodeBody` has an intervening `SignatureHeadLoader.bootstrapProgram`. The diagnostic test is not a Lean source trace of that node body.
- **Temporary scaffold tests:** Active `remaining_tdd.rs` checks expect `NotImplemented`. Retire or replace each such check with behavioral assertions when its stage becomes executable.
- **Ignored ABI smoke tests:** The ignored tests are intentionally red while stubs remain. A dummy halt could pass the simple instruction-table/port smoke gates. Do not promote them to acceptance without imported-Lean traces, semantics, frame invariants and resource accounting.
- **Count fixtures:** Nine small CNFs use an independent raw-literal truth-table oracle, covering no clauses, contradictions, tautologies, empty clauses and unused variables. The actual native end-to-end count is still unimplemented.

**Mutation sanity check:** Changing the initial stack admission condition from `>` to `>=` causes the corrected test to fail; restoring it makes the test pass. This is one targeted mutation, not a mutation-coverage score.

A source refinement claim additionally requires actual Lean execution in the pinned Lean 4.34.1/Mathlib environment, independent state trace comparison, code-table identity checks, protected-frame invariants, and separate primitive TM2 resource verification. No test here establishes an ETH complexity bound.
