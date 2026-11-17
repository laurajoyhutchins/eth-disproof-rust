# Native M1 compiled-query table bridge

Original Lean source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`; `SqrtLogSpace/QueryStreamProgram.lean` blob `c2fb29983bb33229d5cf60729cd3d1e37b9b00ca`.

## Motivation

`QueryStreamProgram.program` is a fixed finite `BitProgram.Program 40 896 l` in the original formalization. Rather than independently reconstructing dozens of interconnected arithmetic and traversal implementations, a genuine imported Lean run can export **the original compiled instruction table**. The Rust `bit_program::Program<40,896>` evaluator then executes that table directly. This is a path to a **literal compiled-program port**, not a host-side #SAT counter or a substitution of test callbacks.

The exporter lives on the Lean reference side in `instrumentation/probes/query_program_dump.lean` (stacked on the original-source instrumentation PR). It must import the original source from the pinned clean checkout. Do **not** copy it into the Rust-only main branch.

## Protocol and operation

The exporter emits to stdout:

```text
PIN|query|<OpenAI source commit>|<QueryStreamProgram.lean Git blob>
PROGRAM|query|40|896|<label count>|<entry>|330|323
CODE|query|0|<source opcode with colon-delimited finite operands>
...
CODE|query|N-1|<source opcode>
END|query|N
```

All 12 source instruction constructors have direct mappings to Rust variants. The importer requires exactly `N` ordered instructions, dimensions 40×896, input 330, output 323, exact pinned source identities, a complete terminal record, and **no trailing data**. It validates each register, stack, and branch target using `Program::new`. Import limits default to 2,000,000 labels and 256 MB; callers may choose smaller or larger explicit limits. Physical runtime capacity is separately controlled by `RunLimits`.

After restoring Lean 4.34.1 and the exact pinned Mathlib and OpenAI source, run the source-reference branch's **attested elaborator-based** exporter from its repository root:

```sh
python3 instrumentation/export_query_table.py --output query.table --max-labels 2000000
```

The wrapper checks both clean Git revisions, the upstream query-source Git blob, and the running Lean compiler version. It then runs `lake env lean` to **elaborate** `query_program_dump.lean`, checks the complete ordered table and writes an atomic SHA-256 receipt next to it. The script uses `Lean.Meta.whnf` to reduce each noncomputable source term to an exact `BitProgram.Instr`, failing on unreduced terms. **Do not use `lean --run`**, because direct executable references to a `noncomputable def` are rejected.

Pinned Lean 4.34.1 standalone compiler testing has exercised this metaprogramming technique on a **toy** noncomputable 40×896 program containing all twelve instruction variants. Its exported table was independently parsed and executed by the Rust CLI. This is a compiler-to-Rust interface test, **not** a real OpenAI query export, Lean/Mathlib import, or mathematical result.

Do **not** treat the table as source-attested merely because its `PIN` line matches. Require the wrapper's real-toolchain provenance and SHA-256 receipt.

The Rust binary reads a finite stack/register fixture, then runs the imported table with limits:

```sh
cargo run --offline --locked --bin native_query -- \
  query.table fixture.txt 1000000 1000000
```

Fixture lines are `STACK|port|bits` (top bit first) or `REG|port|0/1`. One record per physical port; unspecified stacks and registers are empty/false. On a source-defined halt only, the runner prints `HALT|<source steps>|<peak stack bits>|<output stack 323 bits>`. Malformed input, inconsistent port mappings and incomplete runs fail without an answer. This is a **physical-state runner**, not a DIMACS decoder or automatic generator of source-legal query inputs.

## Verification and remaining acceptance

Local Rust 1.99.1: **158 tests in both debug and release** on a retained standalone v0.19 snapshot, including five importer and two CLI subprocess tests; rustfmt and strict Clippy pass. The CLI executes an independent three-label table and rejects a corrupted terminator. The imported-table implementation and tests were uploaded byte-for-byte to GitHub; the complete GitHub branch needs its **own exact-head** build and checks.

**Not yet established:**
- A successful Lean 4.34.1/Mathlib import and `query_program_dump.lean` compilation, reduction, or table export. The upstream `QueryStreamProgram` lives in a `noncomputable` section; actual elaboration/evaluation must be tested, not assumed.
- Whether the full closed instruction table fits practical generation and memory limits.
- One genuine source-legal full query with independent expected output, initial state/encoding, signed pair and reconstruction evidence.
- End-to-end Lean/Rust transition agreement on that exact table, plus resource refusal and protected-frame checks.

Until these pass, `remaining::query::command()` **must remain NotImplemented**. A tiny synthetic table tests the importer, not milestone-one completion. The manual M1 branches remain relevant for source-level debugging and as independent cross-checks.
