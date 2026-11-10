# OpenAI ETH formalization: executable Rust port (v0.4.0)

This is a **source-pinned, dependency-free implementation of the first executable
layers** of OpenAI's Lean ETH development. Source revision:
[`openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
It shares the exact pin in `nonexp-sudoku/reference/lean_eth_source.json`.

## Coverage

| Source Lean definition | Rust code | Status |
|---|---|---|
| `SAT.Literal`, `Clause`, `CNF`, `normalize` | `src/lib.rs` | Executable finite semantics |
| `Encoding.encodeNat`, `frame`, `encodeList`, `encodeCNF` | `src/lib.rs` | Strict wire encoder/decoder |
| `DisjointBranch.childA/B` | `src/lib.rs` | Set-preserving disjoint branches |
| `SparsePriority.select` | `src/lib.rs` | Source-priority finite subset search |
| `SparseCountProgram.step`, `State` | `src/lib.rs` | Semantic counting DFS |
| **`BitProgram.Instr`, `execInstr`, `step`, `initial`** | `src/bit_program.rs` | **All 12 instruction kinds implemented** |
| **`StructuredProgram` and `StructuredCalls` finite compilation** | `src/bit_program.rs` | **Static sequence/if/while/call table compilation** |
| `ProgramLinking.relocateInstr` (identity register/stack maps) | `src/bit_program.rs` | Return substitution and label relocation |
| **`ProgramLinking.liftProgram`** | `src/bit_program.rs` | **Static injective register and stack maps, no runtime port dispatch** |
| **`HighIncidenceProgram.Branches.command`** | `src/native_high.rs` | **Actual 2×2 source-instruction Boolean high-odometer** |
| **`HighCountSeed.command` / `HighCountInit.command` / `initializeCmd`** | `src/native_high.rs` | **Full 40×896 initialization, nested compiled subroutine halts and physical scratch cleanup** |
| **`ExecCNFTupleOdometer.program`** | `src/native_tuple.rs` | **Exact 18-label bit-stack program, complete carry/overflow** |
| **`ExecCNFTupleEnumeration.enumerate`** | `src/native_tuple.rs` | **Compiled start/while/callback/advance loop, including final overflow** |
| **`HighQueryAdapter.highPorts.counter`** | `src/native_tuple.rs` | **Real 40×896 machine mapping: registers 19–21, stacks 789–790** |
| `BitProgramCompile.primitive` and TM2 microsteps | Not implemented | Do not infer primitive time/tape costs |
| `NativeLeafProgram.command k`, `NativeOuter`, `Native.countingProgram` | Not implemented | Primary next execution milestones |
| `FiniteFallback` bounded lookup | Not implemented | Source table is noncomputably chosen |

The semantic DFS's leaf callback remains **bounded exponential enumeration**.
It is **not** a port of the native marked-query leaf and cannot establish ETH's
square-root-log running time or polynomial visited-space guarantee. Rust's
`RunStats` counts *source instructions* and peak live Boolean stack cells,
not TM2 microsteps, physical RSS, or visited tape cells. A faithful compiler
and resource refinement remain separate proof/test obligations.

## Verify on Rust 1.99.1

```sh
cargo fmt --check
cargo test --offline
cargo clippy --offline --all-targets -- -D warnings
printf 'p cnf 3 2\n1 2 0\n1 3 0\n' | cargo run --quiet --offline
# count=5 nodes=3 leaves=2 peak_frontier=2
```

There are 37 Rust tests, including 960 independent structured-program cases
(120 command shapes × 8 input/register states), all short-stack loop cases,
source-derived CNF/golden encoding vectors, strict finite-index checks, exact
branch partitioning, refusal behavior, and subroutine relocation, executable marked-query initialization, its exact instruction counts, mapped subroutines, and dirty-scratch regression cases. They are
**not** tests executed by Lean; the original Lean-vs-Python trace machinery in
the Sudoku repository is a separate reference. A genuine source-executed Lean
vs Rust trace comparison is still required before stating source refinement.

The bit-program interpreter maintains exact live stack-bit counts incrementally
instead of rescanning all 1220 possible stack ports on each instruction.
Mutable public program counters are validated before stepping. Unlike the
unbounded `Fin n` type in Lean, `u128` truth-value masks require an explicit
capacity boundary, enforced by `Cnf::eval_mask_checked`.

## Next source-defined executable boundary

Port one specific component of `NativeLeafRun.command` through the structured
compiler, including its actual marked-query state and physical stack layout;
then expand the verified portion until the full local command is executable.
Avoid introducing an unrelated fast #SAT backend at the semantic leaf seam.
Treat **Lean code table identity, exact output, halt/cleanup invariants,
primitive time, and visited space** as independent acceptance criteria.

## First real native marked-query execution boundary (v0.4.0)

`HighCountSeed.initializeProgram` is the **actual compiled source program**
composed of `HighCountSeed.command` and `HighCountInit.command` from the pinned
Lean sources. The Rust implementation executes physical `BitProgram.Instr`
steps to build a framed zero-assignment odometer from the current high mask.
For `h` high-mask true bits the resulting stack-330 and stack-789 words are
`(1100)^h 0`, i.e. `Encoding.encodeList id (List.replicate h [false])`.

The regression suite checks, for every mask up to seven bits:

- The exact instruction-count formulas from the Lean source, including
  nested compiled halts that become caller return jumps.
- Preservation of the ambient mask and unrelated registers/stacks.
- Clearing of stale scratch, query output, and high-count work stacks.
- Injective register/stack lifting of the 2×2 odometer into the 40×896 ABI.
- Bounded execution refusing instead of treating incomplete work as an answer.

This is now part of the native marked-query **initialization** path, not yet
`HighQueryProgram.marked` or `NativeLeafRun.command` end to end. No source-level
bit-work ceiling or primitive-space theorem follows from these tests.

### Pending real-Lean differential trace

`reference/source-manifest.json` pins the exact upstream Git blob SHAs used
for this increment. `reference/lean_native_high_trace.lean` imports the untouched OpenAI source
modules directly, produces machine-level trace output, and checks halting on
six canonical masks. Run it in the pinned Lean 4.34.1/Mathlib environment with
`LEAN_PATH` including upstream `lean/` and its dependency graph, then run:

```sh
cargo run --offline --quiet --bin native-high-trace > rust-trace.txt
# lake env lean --run reference/lean_native_high_trace.lean > lean-trace.txt
python scripts/compare-native-high-trace.py --lean lean-trace.txt --rust rust-trace.txt
```

The Lean/Mathlib build and **actual** differential run have not been executed
in this package; the needed pinned Mathlib archive is not fully restored in
this VM. The comparator deliberately rejects missing, partial, or malformed
input. Passing the Rust native tests does not substitute for imported-source
Lean execution.

**Next:** extend `HighQueryProgram.marked` from this initialization seam through
the first real `QueryStreamProgram` callback and compare the intermediate
physical stack states, then the full native leaf and outer runner.

## v0.4.0: Physical tuple increment and source-defined callback loop

`ExecCNFTupleOdometer.program` is an actual source-defined **18-label**
finite bit program. This Rust port executes the same instruction table, including
its reversed-prefix scratch operations, carry propagation across framed
little-endian records, cleanup, and complete final overflow. The source
`ExecCNFTupleEnumeration.enumerate` is compiled as a fixed instruction table
consisting of one start instruction, one loop guard, a fixed callback, the
18-instruction increment, and one guard complement. This source control loop
corresponds exactly to `HighQueryProgram.highLoop`, though the substantial
`QueryStreamProgram.command` callback remains **unported**. A two-instruction
diagnostic callback is used in tests; it is not an alternative #SAT oracle.

The independent tests observe every physical counter at the compiled
callback-entry address and check the complete expected visitation order,
including mixed/zero-width tuple components and the final overflow increment.
They also test the actual high-query port map (19,20,21; 789,790), no clobbering
of other stacks, invalid port maps, and capacity refusals.

**Genuine Lean-source differential comparison is still pending** because the
restored pinned Mathlib cache is incomplete (6,056/8,548 compiled modules;
Mathlib A binaries are missing). The repository includes a *directly importing*
Lean trace producer, a Rust trace producer and a strict comparator for **14
cases**, including callback-entry counter snapshots. Run with the pinned
`openai/math` checkout at the recorded blob SHAs and Lean 4.34.1:

```sh
cargo run --offline --quiet --bin native-tuple-trace > rust-tuple.txt
# lake env lean --run reference/lean_native_tuple_trace.lean > lean-tuple.txt
python scripts/compare-native-tuple-trace.py --lean lean-tuple.txt --rust rust-tuple.txt
```

Do not substitute the Rust output into the Lean input: such a self-comparison
validates the parser only, not cross-language conformance. The production
`HighQueryProgram.marked` cannot yet be called or counted from Rust.
