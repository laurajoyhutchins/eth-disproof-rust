# v0.22.0: complete finite predecessor rescan and physical probe

Source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

New source-literal operation constructors in `src/native_signature_candidate.rs`:

- `CounterPrograms.rippleProgram true/false` with exactly 11 labels, preserving the scratch word; `zeroProgram` with exactly 10 labels.
- `CounterForPrograms.testCmd`, `advanceCmd`, and `forCmd` on source 16x24 countdown ports: registers 13,14,15, counter 19, scratch 20. Register 15 is the full-word nonzero result, not its least significant bit.
- `Rescan.body`: copy predecessor 18 to work 12 with scratch 21; execute real full-key `AttainedSignatureProgram.program` on source W=0 and matrix=15; compare complete binary key 14 against saved 17; update one-bit fresh latch 22; clear 12/14; increment predecessor 18 using the original ripple program.
- `Rescan.prepareKey`: compute the candidate's signature once from candidate 16 and keep key on 17. `Rescan.command`: setup fuel by copying candidate 16 to 19, loop while nonzero, then clear predecessor 18 and move the exhausted word 19 to 18. `Rescan.candidateProgram`: compile `prepareKey ; command` on source ports 16 to 22.
- `SignatureTupleNative.candidateMachine`: source-prescribed injective lift to 40x896, with W=141, rows=847, candidate=838, saved key=839, predecessor=844, fresh=362.
- `SignatureTupleNative.probeWith candidateCall`: test *all bits* of remaining fuel 843, branch on available register 38; if nonzero, initialize the physical fresh latch 362, execute the real lifted candidate machine, and copy the one-bit latch into fresh register 39. Preserves the available flag at 38 and all unselected ports.

**Verification:** offline Rust 1.99.1 debug/release tests, strict Clippy, and rustfmt. Independent arithmetic oracles in tests enumerate only small fixed-width input witnesses. Production machine constructs no Rust list of predecessors and calls no host-language arithmetic or signature comparison. Empty heads, empty matrices, collisions and unique signatures, two-row signature ordering, three-bit assignments, arbitrary register poison, retained caller stacks, and capacity refusal are tested.

**Remaining:** the full `SignatureTupleComplete.command` DFS is not assembled, `SignatureTupleLoader.loadHead` and `QueryVisitorProgram.visitor` still need independent native composition, and signed pair commit / node finishing remain. No imported Lean/Rust differential trace or ETH theorem claim is established. The current suite exercises a standalone source snapshot, not the combined GitHub branch or remote CI.
