# Source-defined head selection and support

Pinned upstream: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

`src/native_head_selection.rs` ports the concrete Boolean-stack instruction
programs used by `LeafHeadSetupProgram.heads`:

- `ArrayPrograms.countedCopyProgram` and `ArrayUpdatePrograms.readProgram` (38 labels).
- `SubexpHeadColorProgram.Prefix.program`, `select`, and `command`, using the
  source's preserving indexed read and literal one-hot bit prefix counter.
- `Subexp.TypeBitProgram.program` (7 labels), including out-of-range false.
- `HeadIdentifierProgram.test`, `visit`, `loop`, and the complete
  `FullTable.program`, including descending visits and 16-register reset.
- `LeafHeadSetupProgram.heads` under `LeafHeadSetupProgramStorage.stage`:
  low-bank inputs 128→30, 134→31, 649→32, 133→33, 132→38; returned
  outputs 0→650 (framed selected IDs) and 1→651 (zero-form count).
- `heads_support = seq heads support`, reusing the previously ported
  `LeafHeadSetupProgram.support` stage to produce stack 652 (unary selected
  count) and 670 (ambient head mask).

Both selectors operate on the original flattened word table and coordinate
indices. They do not replace the program with a host-language `filter` or
bit-vector splice; the independent expected-value tests use direct reference
calculations only as assertions.

## Local verification

```sh
cargo test --offline --test native_head_selection
cargo test --offline
cargo test --offline --release
cargo clippy --offline --all-targets -- -D warnings
cargo fmt --check
```

Eight new tests cover exact array-read and one-hot decoder instruction counts,
uniform-width source retention, lower-level indexed bits including missing
positions, full prefix selection, original-ID ordering, preservation of
unselected tail rows, dirty work bank cleanup, and integration with the staged
support machine. The reconstructed local source passes 120 tests in debug and
release, including existing head support and scatter tests, on Rust 1.99.1.

The input conditions from Lean remain preconditions: the actual source machine
does not validate malformed unary metadata or inconsistent row widths before
execution. Runtime instruction and stack-bit limits fail closed rather than
relabeling incomplete computations as successful results.

The full `LeafHeadSetupProgram.prepareHead` is **not implemented**: it still
requires executable `LeafHeadFactorsProgram` and subsequent signed matrix
arithmetic. These Rust tests have not executed the original Lean source, nor
do they establish any ETH theorem or primitive-machine cost refinement.
