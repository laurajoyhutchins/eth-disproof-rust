# Experiment: Lean instruction tables compiled to Rust

This experimental branch lowers serialized, pinned finite BitProgram instruction tables to direct Rust control flow. It does not implement the full ETH native counter or establish theorem resource bounds.

## Reproduce

With Rust 1.99.1, from rust/lean_eth_reference:

    cargo test --locked --offline --test lean_table_codegen
    cargo test --locked --offline --bin lean-table-codegen
    cargo run --locked --offline --bin lean-table-codegen -- --fixture tools/fixtures/tiny.table /tmp/compiled_fixture.rs

Cargo build.rs regenerates the synthetic fixture into OUT_DIR, and the integration test compiles the resulting Rust code. It independently constructs the same 16-label machine using Program<4,3> and compares results, source-instruction counts, peak stack bits and complete machine state, including partially executed configurations under resource refusal.

The fixture covers all 12 source instruction variants. It is explicitly synthetic; no Lean-source attestation is claimed.

## Authentic query mode

    cargo run --locked --offline --bin lean-table-codegen -- /path/to/attested-query.table /tmp/query_generated.rs

Default mode requires the exact query table protocol used by the adjacent Lean exporter and Rust importer: source SHA, Git blob, 40 registers, 896 stacks, entry, 330/323 I/O ports and ordered complete labels. The generator accepts only well-typed numeric operands. The generated Rust executes physical operations directly; it does not call a SAT oracle, a table interpreter or untrusted embedded Rust.

This is deliberately a small-program experiment, with an 8 MB input limit and 8,192-label generator limit. Larger programs require a measured chunked code-generation strategy and compiler-resource budget.

## Evidence boundary

Passing the generated fixture tests would demonstrate local Rust interpreter-to-Rust compilation parity on the tested finite cases. It does not demonstrate real original-Lean export, imported-Lean differential equivalence, extraction of the noncomputable full query table, end-to-end native SAT counting or an asymptotic complexity result.

The next accepted increment should be one genuine small table exported from pinned Lean 4.34.1 and Mathlib, checked against both the imported Lean execution trace and the generated Rust machine trace. Preserve the native readable Rust port separately.


## Local reproducibility evidence (2026-11-10, Rust 1.99.1)

Restored the SHA-256-verified official Rust 1.99.1 Linux x86-64 archive from the user's Library. Reconstructed the complete generator/build/CLI/test files byte-for-byte: each new source file's local Git blob hash matched its GitHub blob hash after rustfmt.

On the retained lean_eth_reference v0.21.0 local source snapshot, with the experiment's exact formatted new files:

- cargo fmt --all -- --check: passed
- cargo test --locked --offline --all-targets: passed, including the three new generator/compiled-fixture tests
- cargo clippy --locked --offline --all-targets -- -D warnings: passed
- cargo test --locked --offline --release --test lean_table_codegen --bin lean-table-codegen: 3 passed
- The test matrix executed 3,024 differential comparisons of machine run outcomes, source-instruction and peak-bit stats, and all physical registers/stacks at both successful and refused prefixes; additionally checked an invalid program counter.
- The CLI-emitted Rust bytes exactly matched Cargo build.rs output; generated fixture SHA-256: bf1719240d7349c3e0457d0b2a30e19ece494e24375e41a5f76e32ea0c39dbe5.
- Strict query mode rejected the same synthetic table without --fixture and produced no output artifact.

**Scope of evidence:** this compilation was on a retained v0.21.0 local source snapshot, not a fresh complete checkout of the current GitHub branch against main. No GitHub exact-head CI status or genuine imported original Lean execution was available at the time of recording.

## Source-derived Rust, not just synthetic fixtures (2026-11-10)

The following *original* executable declarations were extracted from the pinned
`openai/math@4eaee87548250b2682affda7d05d947c05554bae` source snapshot:

| Program | Original Git blob | Registers × stacks × labels | Executable Rust |
| --- | --- | --- | --- |
| `BinaryPrograms.Add.program` | `ab8a858c2466aa3879087f825802aa76c7aa768f` | 8×3×13 | Cargo-generated `original_binary-add.rs` |
| `QueryProgram.parityProgram` | `7a2535f7c479463a5f5ed8a30a33192aad1b063e` | 3×1×4 | Cargo-generated `original_query-parity.rs` |
| `TypeBitProgram.program` | `4e020c828e458b4420179da94c3451bea653a7b9` | 3×2×7 | Cargo-generated `original_type-bit.rs` |

The pinned-source extractor `src/bin/extract-lean-tables.rs` verifies each
**entire original Lean file's Git blob hash**, the declaration, the machine ABI,
its ordered literal instructions, and label count. It refuses arbitrary Lean
expressions or unsupported computation rather than inventing the result.
`build.rs` verifies the table's pin, ABI and instruction indices, and compiles
direct Rust machine steps. No runtime instruction interpreter is called by these
generated functions.

To regenerate from a checkout containing the pinned original source:

```sh
cargo run --locked --offline --bin extract-lean-tables -- \
  --upstream /path/to/openai-math \
  --output-dir tools/fixtures/original --legacy

cargo fmt --all -- --check
cargo test --locked --offline --all-targets
cargo test --locked --offline --release --test original_lean_codegen
cargo clippy --locked --offline --all-targets -- -D warnings
```

Hashes of the canonical source tables:

- `binary-add.table`: SHA-256 `278285aea7db76bc61c87effdab8730b89d6523c9d95327452dd4bf45a11bad6`
- `query-parity.table`: SHA-256 `55b6224683cfc84b2a4439c267b855576511a882cffa65abeb423656bcf00856`
- `type-bit.table`: SHA-256 `80361c4c5531a1bca45b98bf5e654ca3b72d40e76dba9a3e3d6264a7af5e51f2`

### What was actually executed

Restored the SHA-256-verified Lean **4.34.1** binary from the user's archived
toolchain. The three exact source declarations were inserted into a *standalone*
Lean verification harness with the original `Instr` and `Program` definitions;
the only changes needed for the standalone import-free harness were replacing
Mathlib's finite-vector notation with the equivalent exhaustive `Fin` match
and omitting the unavailable `Fintype` deriving clause. **Lean compiled and
executed the actual declarations**, and all three emitted tables compared
byte-for-byte with the independent pinned-source extractor.

Rust **1.99.1** was restored and the source-generated code was compiled on the
retained v0.21.0 reference-crate snapshot. `cargo fmt`, complete offline locked
all-target tests, and strict Clippy passed; four additional generated-original
tests passed in debug, and the release test passed. The binary addition test
checks all 16,384 pairs `0..127 × 0..127` against independent integer addition;
the parity test checks both initial parity values on every word of length
0–8; the indexed-bit test checks both in-range and out-of-range access and
stack cleanup. Resource-refusal behavior is also exercised.

**Evidence limits:** The standalone Lean harness is not an imported, built
original OpenAI theorem environment. The full `QueryStreamProgram.program`
still depends on the missing complete Mathlib/OAI compiled closure, includes
`noncomputable` declarations, and may require an infeasibly large finite
table. No full query or native counter has been extracted or run. The complete
GitHub PR checkout still requires its own exact-head CI result. Do not count
these source-defined subprogram tests as a Lean/Rust refinement proof or ETH
time/space result.


## Complete mechanically extractable literal-program catalog

The scan of all 3,977 Lean files in the original pinned
`lean/OAI/Algorithms/SubexponentialSAT` tree found **61** closed,
fixed-dimension `BitProgram.Program` declarations whose instruction tables
are written literally as `![...]` or a finite `match q.val`.

All **61** were compiled into direct Rust control-flow functions. This includes
sparse label matches with an explicit final fallback, and symbolic labels
only when defined in the same file as closed `Fin N := numeric-literal`
declarations. No arbitrary elaboration or expression evaluation is accepted.
The scanner now reports **zero unsupported declarations in this narrowly
defined syntactic category**. Other composed `Cmd` programs are outside this
category and are **not counted**.

The canonical complete inventory is
`tools/fixtures/original/all-literal.tsv` (61 rows, source paths, Git blob
identities, machine ABI and per-table SHA-256). The corresponding 61 canonical
instruction tables are in `tools/fixtures/original/all-literal.bundle`.

- Original source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
- All **52** distinct upstream source-file Git blobs (including the two
  source-control-flow exceptions formerly unsupported) were independently
  checked against the GitHub contents at the exact original commit; every
  recorded blob matched.
- `src/bin/extract-lean-tables.rs --check` re-derives and compares the canonical
  manifest and bundle from an original source checkout.
- Cargo `build.rs` checks the source pins, dimensions, labels, entries,
  ports and every finite instruction record before generating
  `OUT_DIR/original_catalog.rs` (202,626 bytes of actual Rust code).
  There is no external Cargo dependency.
- `tests/original_literal_catalog.rs` reconstructs an independent
  `Program<R,S>` from each original literal table, and compares that
  interpreter against the **separately compiled generated Rust** for all
  61 programs across a matrix of eight initial configurations, six
  instruction limits and three stack-bit limits. This is **8,784**
  differential executions, comparing the entire machine state and result
  on success and refusal, not only final output.
- On the retained local v0.21.0 Rust reference source snapshot, verified Rust
  1.99.1 `cargo fmt`, offline locked all-target tests, release-mode
  original-program tests and strict Clippy all passed. The exact updated
  GitHub PR checkout still needs a separate combined-head CI result.

Command to independently rebuild the catalog from authentic source:

```sh
cd rust/lean_eth_reference
cargo run --locked --offline --bin extract-lean-tables -- \
    --upstream /path/to/original/openai-math \
    --output-dir tools/fixtures/original --check
cargo test --offline --locked --test original_literal_catalog
```

**Boundary:** a literal instruction-table declaration is not the same as the
full noncomputable, heavily composed `QueryStreamProgram.program`.
The original full query exporter remains blocked on an import-capable Lean
4.34.1 + pinned Mathlib runtime and may still exceed finite table/codegen
budget. A full native SAT count, genuine imported-source parity and ETH
complexity claims are not established here.

The Rust scanner accepts only literal vectors, finite label matches, and finite conditional tables, reusing the Rust code generator to reject invalid machine control indices. The bundled tests exercise these formats and refusals. They do **not** substitute for a fresh `--check` against the complete pinned original Lean checkout.
