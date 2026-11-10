# OpenAI ETH formalization: executable Rust port (v0.10.0)

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
| **`HighQueryAdapter.prepareHigh`** | `src/native_query_prefix.rs` | **Actual masked-assignment query-stream prefix, physically compiled** |
| **`HighQueryProgram.copyHighCounter`** | `src/native_query_prefix.rs` | **Physical durable-counter copy before query execution** |
| `ParserProgram.frameProgram`, `AssignmentRecordViews.flattenProgram` | `src/native_query_prefix.rs` | Exact finite parser and framed-record flattening |
| `HighIncidenceProgram.Restriction.program` | `src/native_query_prefix.rs` | Exact high/low coordinate merge |
| **`NativeLayoutLoad.command`** | `src/native_layout.rs` | **17 port clears and 14 parked master copies; exact nested finite source tables** |
| **`PairNativeSetup.CountFalse.command`, `setupCaller`** | `src/native_pair_setup.rs` | **Actual free-coordinate tally, isolated scratch, metadata staging** |
| **`LeafHeadSetupProgram.Address.command`, `initializeAddress`** | `src/native_bootstrap.rs` | **Unary multiplication and finite 16×768 staged address initialization** |
| **`SubexpSunflowerProgram.CountRecords`, `countRows`** | `src/native_bootstrap.rs` | **Exact 13-label framed-record counter and staged record count** |
| **`LeafHeadSetupProgram.retainCache`** | `src/native_bootstrap.rs` | **Preserving 640–642→710–712 copies; exact instruction counts** |
| `BinaryPrograms.Add.program`, `Add.littleEndianProgram` | `src/native_integer_cache.rs` | **13 / 17 source-defined instructions; exact carries and bit order** |
| `LayoutProgramScalar.cacheCellLocal`, `cacheCell` | `src/native_integer_cache.rs` | **Executable H recurrence cell** |
| `LayoutProgramScalar.initialCommand`, `initialBuild` | `src/native_integer_cache.rs` | **Framed initial H row with runtime width** |
| `LayoutProgram.IntegerCache.copies`, `makePower` | `src/native_integer_cache.rs` | **Executable prefix / denominator suffix; no H-flat substitution** |
| `LayoutProgram.IntegerCache.program`, complete `SignatureHeadLoader.bootstrapProgram` | Not implemented | H-table iteration and width normalization remain |
| `BitProgramCompile.primitive` and TM2 microsteps | Not implemented | Do not infer primitive time/tape costs |
| `NativeLeafProgram.command k`, `NativeOuter`, `Native.countingProgram` | Not implemented | Primary next execution milestones |
| `FiniteFallback` bounded lookup | `remaining::outer::finite_fallback` | Explicit fail-closed stub: noncomputable Lean table |

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

There are 71 Rust tests, including 960 independent structured-program cases
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

## First real native marked-query execution boundary (v0.5.0)

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


## v0.5.0: First actual query-stream command executes

The previous v0.4.0 callback was diagnostic only. The new `native_query_prefix`
module implements the first **actual command** in `QueryStreamProgram.command`,
namely `HighQueryAdapter.prepareHigh`, with its physical `BitProgram`
instruction table. It also ports the immediately preceding
`HighQueryAdapter.copyHighCounter` from `HighQueryProgram.conditioned`.

The real query-stream prefix is therefore:

1. Copy the current framed high-counter stack `789` to query stack `330`;
   leave the durable counter intact, clearing scratch `792`.
2. Clear stale high-context stacks (including old `703`) using the exact
   source clear programs.
3. Decode the query assignment by running the source seven-label frame
   parser and the source framed-record flattener (not by indexing a Rust array).
4. Reverse the original high mask, merge the supplied assignment into
   ambient coordinates, and emit the complete reversed bit vector on `703`.

The source-defined `prepareHighProgram` has exactly **85 finite control
labels**, irrespective of mask size. A source-composed `query_stream_prefix`
callback executes within the actual `ExecCNFTupleEnumeration` high loop,
producing the correctly aligned vector for each visited assignment, followed
by the real overflow increment. All data resides on the original
`40 × 896` machine ports.

The additional six tests exhaust all high assignments across Boolean masks
up to six coordinates (and test actual high-loop visits up to four), verify
individual parser/transfer/flatten/merge *instruction counts*, dirty-scratch
cleanup, retained counter and ambient registers, exact coordinates, and
bounded termination. The tests use a separate direct mask/assignment model
for expected outputs. **43 tests pass on Rust 1.99.1** in both debug and
release, with strict Clippy and formatting checks.

`reference/lean_native_query_prefix_trace.lean` imports the original pinned
OpenAI program and traces six physical input cases using its `BitProgram.step`.
The matching Rust trace producer and strict comparator are:

```sh
cargo run --quiet --offline --bin native-query-prefix-trace > rust-prefix.txt
# Run only with pinned Lean 4.34.1 and a *complete* matching Mathlib cache:
# lake env lean --run reference/lean_native_query_prefix_trace.lean > lean-prefix.txt
python scripts/compare-native-query-prefix-trace.py \
  --lean lean-prefix.txt --rust rust-prefix.txt
```

**This Lean trace has not been executed.** The existing Mathlib cache is
incomplete, and no source-level differential pass is claimed. The actual
`QueryStreamProgram.nodes`, pair DFS, ring interpolation, signed accumulation,
`QueryReconstruction`, and the full native leaf still need executable ports.
This source prefix does **not** compute a query count and does not establish
an ETH-disproving complexity bound.

## v0.6.0: Native interpolation-node cursor and framed reader

The actual first two commands in `QueryStreamProgram.nodes` now execute:
`QueryAssembler.Nodes.initializeNodes` and `QueryNodeFinish.guardCursor`.
This includes the physical copy of the produced framed interpolation-node
table from stack 300 onto cursor 301, all source-defined scratch/index clears,
and the non-consuming loop guard peek (registers 37/38).

`QueryAssembler.Nodes.beginNode` also executes through the real `RecordPrograms`
frame parser and `RingNodeSetup.readNode`, placing the current node on stack 78
and preserving the unread suffix of the cursor on stack 301. The separate
`QueryNodeFinish.finishNode` control suffix is ported (cleanup, unary index
advance, guard refresh), but **not** its preceding signed coefficient result
append. Tests include a clearly marked diagnostic loop using the real reader
and control suffix; that loop is **not** the source `QueryStreamProgram.nodeLoop`.

The source-composed `query_nodes_entry_command` executes `prepareHigh` followed
by exactly the two node-entry commands, stopping before the native pair and
interpolation calculations. Tests independently verify framed records, exact
source instruction counts, dirty scratch cleanup, high-bank preservation,
zero-record handling, and the diagnostic index/cursor lifecycle.

A new paired trace harness imports the *original pinned Lean source* directly:

```sh
cargo run --offline --quiet --bin native-nodes-trace > rust-nodes.txt
# With complete pinned Lean 4.34.1/Mathlib environment ONLY:
# lake env lean --run reference/lean_native_nodes_trace.lean > lean-nodes.txt
python scripts/compare-native-nodes-trace.py --lean lean-nodes.txt --rust rust-nodes.txt
```

The full imported-source Lean differential run remains **UNEXECUTED** in this
VM due to the incomplete pinned Mathlib cache. This implementation has not
executed the native node/pair arithmetic or proved any ETH complexity claim.


## v0.7.0: node layout loading and physical pair initialization

The source-pinned `NativeLayoutLoad.command` is now fully executable as a
**167-label finite instruction program**. It clears 17 named scratch/low ports,
then loads 14 parked source masters from 730–743 into 128–141 using the
source-prescribed preserving-copy subroutines. Both nested `liftCommand`
compilation boundaries are retained. Independent tests verify the exact
source-instruction cost, all 14 word mappings, register/stack frames, and
explicit word/peak-live-stack bounds over dirty initial states.

The new `first_node_layout_prefix_command` composes the existing actual
`prepareHigh`, node-table initialization, non-consuming guard, one native
node read, and `NativeLayoutLoad`. It stops **immediately after the first
node layout load**, using a one-iteration branch rather than pretending to
implement the full `QueryStreamProgram.nodeLoop` without its arithmetic.

The source-defined `PairNativeSetup.setupCaller` is also ported, including:

- `CountFalse.command` and its `UnaryForPrograms` counted loop, which
  physically emits one unary bit per *false* high-mask coordinate.
- `SubexpSetupStorage.isolated` preparation, compiled callback invocation,
  result transfer and complete scratch-bank cleanup.
- Actual count output on stack **832**, preserved metadata copied from 243
  to **833**, and the clears on 834/835.

The new tests exhaust all Boolean masks up to eight bits for the local count
and up to seven bits for the full 40×896 caller. They check exact instruction
formulas and that scratch and unrelated persistent state are preserved or
cleared as prescribed. **58 tests** pass on pinned Rust 1.99.1 in both debug
and release, with formatting and strict Clippy checks.

Direct imported-source Lean/Rust differential fixtures are prepared:

```sh
cargo run --offline --quiet --bin native-layout-pair-trace > rust-layout-pair.txt
# Requires complete Lean 4.34.1 / pinned Mathlib source build:
# lake env lean --run reference/lean_native_layout_pair_trace.lean > lean-layout-pair.txt
python scripts/compare-native-layout-pair-trace.py \
  --lean lean-layout-pair.txt --rust rust-layout-pair.txt
```

The original Lean fixture has **not been executed** due to the incomplete
Mathlib cache. The original `SignatureHeadLoader.bootstrapProgram` lies
between layout load and pair setup in the source graph and is **not** ported.
These independently executable stages are not falsely concatenated into one
complete program. The actual signed pair iteration, signature tuple DFS,
ring evaluation, canonical query reconstruction and the full ETH-disproving
program remain unimplemented. No source-level cross-language refinement or
complexity guarantee is claimed.


## v0.8.0: Entire remaining executable path stubbed, no false successes

All remaining **runtime** stages from the native query through the proof-facing TM2 compiler are now represented by typed fail-closed entry points in `src/remaining.rs`. This includes signature bootstrapping, pair DFS, tuple visitor, ring reconstruction, marked/accepted high queries, greedy leaf rounds, native leaf lifting and terminal dispatch, outer DFS, frontend/fallback, final counting program and primitive compiler. `STAGES` provides the pinned Lean source symbols, machine dimensions, and prerequisites. Every unported function returns `Error::NotImplemented` rather than an accepting halt or an enumerating oracle. See [`docs/remaining-lean-port.md`](docs/remaining-lean-port.md). **No additional stage becomes executable in v0.8.0.** The original 58 tests are unchanged; the three new scaffold tests require a local toolchain run.

## v0.9.0: concrete signature-head bootstrap prefix

`src/native_bootstrap.rs` ports the actual unary address computation, 13-label framed-record count, their isolated stage copies and cleanup, and the final preserving cache-retention suffix. Six source-derived tests exercise values, exact source instruction counts, register and stack frames, dirty scratch and the `40×896` node lift. The new six tests passed locally together with all 58 pre-existing executable tests, using Rust 1.99.1 offline; the separate three-test v0.8.0 scaffold has not been rerun in that local snapshot.

**This is deliberately not the complete `SignatureHeadLoader.bootstrapProgram`:** `LayoutProgram.IntegerCache.program` has not been ported. Cache retention is an independent suffix and is not called by the prefix. No source-executed Lean/Rust differential, full node callback, TM2 bound or complexity theorem has been established by this increment.


## v0.10.0: integer-cache finite arithmetic and initial H row

Source-pinned physical Rust programs now execute the original 13-label binary adder, its 17-label linked little-endian variant, the H recurrence cache cell, framed initial H row, fixed integer-cache copy prefix, and the unary denominator constructor. Seven new local tests pass in debug and release; the native package's full 71-test suite passes, as do formatting and strict Clippy. See [`docs/integer-cache-port-v0.10.md`](docs/integer-cache-port-v0.10.md).

The complete `LayoutProgramScalar.hFlatProgram` remains unported. **Neither the complete integer cache nor `SignatureHeadLoader.bootstrapProgram` is executable**, and no imported-source Lean differential is claimed.
