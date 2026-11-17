# What the tests can establish

This is a test-design audit, not an independent Lean conformance
certificate. For the **current accepted main tree**, use the
[execution/evidence matrix](evidence.md) and the exact GitHub Actions run
for the commit you are reviewing.

| Test family | Positive evidence | Does not prove |
| --- | --- | --- |
| Finite CNF count fixtures | Rust finite semantics agree with independent small-input raw-literal enumeration | Native counting or a non-exponential algorithm |
| `BitProgram` instruction tests | Rust interpreter state, stack/register behavior, bounds and halt cases on tested inputs | Independently executed source Lean equivalence |
| Native frontend integration | The runnable Rust `Native.frontendCommand` preserves required source ABI ports and reports instructions/peak stack bits | A #SAT answer or full native counting pipeline |
| Stage/registry tests | Source-path pin *format*, graph uniqueness, ordered prerequisites, refusal boundaries | Byte-for-byte source equivalence or original Lean execution |
| Synthetic seam/composition tests | Invariants for the specific Rust components assembled in each test | Equivalence of a different full original source command |
| Ignored scaffold smoke tests | Information about tests intended for future implementation work | Successful implementation merely because they compile or are ignored |

## Remaining high-value tests

- Execute the genuine pinned original Lean `BitProgram.step` and the Rust
  interpreter independently. Compare all machine state and outputs after
  **every** transition, including dirty unrelated state, scratch cleanup,
  step limits, capacity failure and halting.
- Use adversarial and generated inputs for stack underflow/overflow,
  aliasing, high-index registers, bitword order, integer limits, and illegal
  encoded formulas. A local Rust-vs-Rust oracle does not replace Lean.
- Complete a source-defined **nonterminal** count without an enumerating host
  fallback. Test its full chain from input encoding to answer.
- Report source instruction counts, Rust allocations and runtime separately
  from primitive TM2 transitions, tape occupancy and any theorem-level
  asymptotic bound.

A previously performed mutation of the initial stack admission guard
(`>` versus `>=`) was detected by a focused Rust test. That observation
does not establish broad mutation coverage.

When a stage becomes executable, replace any test that only expects
`NotImplemented` with meaningful behavior checks and leave negative
refusal cases for the stages that remain unimplemented.
