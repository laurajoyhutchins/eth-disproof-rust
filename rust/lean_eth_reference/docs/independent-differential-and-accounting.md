# Independent Lean/Rust execution and resource evidence

The acceptance boundary is an actual **two-producer** execution of the same
pinned original source. A Rust test that agrees with a Rust model is not Lean
differential evidence; matching final #SAT answers is not instruction equivalence.

## Source-machine differential

The import-side observer in `reference/lean_full_machine_trace.lean` calls
upstream `BitProgram.step` on the unmodified `SqrtLog.HighIncidenceProgram.Branches.program`.
The Rust observer `src/bin/lean-full-machine-trace.rs` calls the corresponding
port and emits **every** (label, registers, complete stacks) state through halt.
The two trace producers are run independently, with 62 boundary/dirty cases.

```sh
cd rust/lean_eth_reference
scripts/verify-lean-differential.sh --lean-repo /path/to/pinned/openai-math --suite full
# all available source-instrumented suites:
scripts/verify-lean-differential.sh --lean-repo /path/to/pinned/openai-math --suite all
```

The five snapshot suites (`high`, `tuple`, `layout`, `nodes`, `query`) use one
native Rust `compare-traces` executable with suite-specific mandatory keys,
field counts and physical-word checks. The full-state comparison, physical
resource profiling, and SHA-256 receipt generation now use the Rust
`full-machine-evidence` executable. They have strict negative tests under
`cargo test --all-targets`. Neither comparator authenticates a trace file:
only fresh independent execution of the pinned Lean producer establishes
its provenance.

The wrapper refuses non-pinned sources, wrong Lean/Rust versions, missing
Mathlib, a failed real `import Mathlib`, non-halting traces, and mismatched
physical states. It removes stale receipts before running. The `full` gate
now also independently runs an instrumented Rust producer, reconciles every
per-opcode transition count against the Lean/Rust traces, and hashes the cost
reports into its receipt.

**At the time of authoring, the genuine Lean gate has not passed.**
A missing/incomplete Mathlib cache is an explicit BLOCKED state, not a skip,
golden-answer replacement, or a successful independent differential test.

## One actual source-native counting slice

```sh
cd rust/lean_eth_reference
printf 'p cnf 3 0\n' | cargo run --locked --offline --bin eth -- terminal-count
printf 'p cnf 3 1\n0\n' | cargo run --locked --offline --bin eth -- terminal-count
```

For terminal normalized CNFs, the native Rust port executes three **source
BitProgram command families plus an explicit source-primitive port adapter**, retaining the same 80-register/1220-stack machine
state across the boundaries:

1. `Native.frontendCommand` performs physical CNF normalization.
2. `NativeTerminal.readyCommand` classifies and constructs the physical
   little-endian count on stack 263 (0 for an empty clause; 2^n for no clauses).
3. A deliberately explicit source-primitive adapter copies the count from 263
   to the actual answer ABI input port 256, replacing the preserved formula.
4. `Native.answerCommand` preserves the count and writes positivity to 1216.

The source count/answer ports **do not line up** in the shortened
terminal pipeline. The original `Native.outerCommand` must establish a count
on `ABI.countStack = 256`, but `NativeTerminal.readyCommand` places its
intermediate result on 263. To make a complete *bounded terminal path*, an
explicit fourth stage physically clears 256 and preserves/copies 263 → 256
using source-defined `StackRoutines.clearProgram` and
`StackRoutines.copyProgram`. This is an **adapter**, not a claim that the
original outer DFS counting program was reproduced. The answerCommand then
reads the correct ABI count input. The preserved original CNF input is
asserted **before** the adapter deliberately replaces stack 256.

All stages execute without `EnumeratingLeaf`, `Cnf::normalize`, a host-side
SAT predicate, or an invented nonterminal command. Decimal formatting is a
post-halt representation conversion and supports counts beyond 128 bits.
A nonterminal formula **fails closed** with `NotImplemented`, rather than
becoming a successful false/zero answer. The complete recursive/nonterminal
ETH #SAT engine is NOT implemented by this slice.

## Three disjoint resource accounts

| Account | What is observed | What is *not* concluded |
| --- | --- | --- |
| Mathematical source machine | Each `BitProgram` instruction, PC, register/stack transitions, peak live stack bits, final count/answer | Primitive two-tape TM2 step bound |
| Rust implementation | Per-opcode `Instant` elapsed nanoseconds, global-allocator alloc/realloc calls during `step()`, requested heap bytes, max VecDeque capacity | Lean allocation/time, process RSS, speed without profiler overhead |
| Formal theorem | Requires the original `BitProgramCompile`/TM2 reductions and justified encoding/space conversions | Not derivable from Rust instruction count or CPU runtime |

For the bit-level program, **integer bit-width is not applicable** because its
source registers and stacks are Boolean. Numeric count words have length in
bits; any future host bigint implementation must instrument its own maximum
operand/result sizes. Stack capacity is not tape usage. Requested bytes are
not live heap bytes. Timings include probe overhead.

```sh
cargo test --locked --offline --all-targets
cargo test --locked --offline --all-targets --bin full-machine-evidence --bin compare-traces
```

The seeded physical-machine tests cover all 12 opcodes, empty/nonempty
stacks, overlapping register ports, halt idempotence, exact step budgets,
malformed addresses, unsigned 128-bit boundaries, overflow refusal, and
nonterminal semantic refusal. Follow-on work should add an authenticated
Lean trace for the terminal counter composition itself, then extend the
source-native path to **one real nonterminal formula** before claiming a
general counter.

## Live instrumented Rust per-stage profile (no Lean assertion)

```sh
cd rust/lean_eth_reference
cargo run --release --locked --offline --bin profile-full-machine -- --terminal > terminal-profile.csv
```

This profiler independently executes four physical 80×1220 source-instruction
stages and reconciles their count words, final answer, stage instruction counts
and cumulative budget with the uninstrumented native terminal runner. It
reports per-stage per-op timing and allocation *requests*; it increments peak
live stack bit counts and runtime stack capacity observations on push/pop,
without a full-stack scan after every instruction. Samples include n=0,
n=3 no clauses, n=3 empty clause, and a normalized tautology.

This **does not** claim to measure primitive TM2 operations. Running this
profiler is separate from a genuine imported-Lean full-state comparison.
A fair evaluation of interpretation overhead needs an uninstrumented runtime
baseline as well, because these measured times include observer costs.
