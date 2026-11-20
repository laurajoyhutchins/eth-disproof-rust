# Contributing

This is a source-pinned research port. Each change should make the executed
behavior or the boundaries of the original Lean construction easier to audit.

See [Writing these notes](docs/STYLE.md) for the editorial conventions: equations, counterexamples and source identities before status language. The same standard applies to PR descriptions.

## Contribution contract

A pull request should answer four concrete questions:

1. **Original source:** Which Lean symbol, file and pinned Git revision is the
   implementation based on? See the [source manifest](eth/reference/source-manifest.json).
2. **Execution:** Is the change an instruction-level source port, a host Rust
   semantic helper, a separate optimization, or a proof-only argument?
3. **Evidence:** Which tests were run on the **exact PR head**, with what
   commands and outputs? For Lean parity, actually execute the pinned
   original Lean implementation and compare all state transitions and halting,
   rather than replaying committed golden fixtures or a second Rust oracle.
4. **Limitations:** What remains unsupported? An absent native stage must
   return an explicit refusal, never a zero count, synthetic halt or silent
   fallback to bounded exponential enumeration.

Keep changes reviewable: one source-defined behavior or one distinct argument
per PR. Do not combine source-faithful translation, performance optimization,
and new mathematical conjectures without separately testing each claim.
Follow the [PR template](.github/PULL_REQUEST_TEMPLATE.md) and
[execution/evidence matrix](eth/docs/evidence.md).

For Rust implementation and diagnostic binaries, follow the
[Rust code conventions](docs/RUST_STYLE.md). Keep style-only changes separate
from Lean correspondence and algorithmic changes.

## One Lean-to-Rust compiler path

The authoritative language pipeline is **Lean 4 source → Lean frontend and
compiler → final ownership-explicit compiler IR**. Extend the one in-process
Rust backend in `compiler/`. Do not add another surface
parser, independent IR optimizer, parallel code generator or silent fallback
to a source-graph substitution.

When changing this backend:

1. Identify the original Lean declaration, pinned compiler-IR construct,
   executable closure and borrow/ownership convention. Preserve source names
   and recorded dependency identities.
2. Lower into the one emitter, retaining explicit `inc`/`dec`/`del`,
   borrow, move, call, reuse and release decisions. Rust `Rc`
   handle counts are not Lean source reference counts by default.
3. Keep generated Rust's runtime dependency explicit. The **first**
   correspondence target is the pinned Lean C runtime through FFI.
   Only promote a Rust-native runtime operation after comparing it
   against that reference on the admitted domain.
4. Make unsupported IR, externs and ownership shapes refuse as a whole
   without publishing partial output. Bind accepted evidence to the
   exact source and PR-head revisions.
5. Compare independent Lean results and, for sharing-sensitive code,
   observed object identity, allocation, release and reuse. Golden
   output-only tests cannot certify ownership fidelity.

The existing standalone GMP/`Rc` runtime remains an implementation
of a **bounded tested subset**, not the baseline proof of physical
runtime equivalence. LCNF inspection informs analysis; it is not
another backend. A Rust proof kernel is a separate project.

The [architecture](compiler/docs/backend-first-architecture.md),
[execution runtime contract](compiler/docs/execution-runtime-contract.md)
and [compiler status](compiler/docs/compiler-status.md)
identify what is implemented, proposed or still unsupported.
Original ETH QueryStream residualization is G2, not a reason to
weaken G1's IR contract.

## Run local checks

From the repository root, `rust-toolchain.toml` pins Rust **1.99.1**
with rustfmt and Clippy:

```sh
cargo fetch --locked
cargo fmt --all -- --check
cargo test --locked --offline --all-targets
python3 -m unittest discover -s eth/tools -p 'test_verify_source_graph.py'
cargo clippy --locked --offline --all-targets -- -D warnings
```

The workspace reuses locked dependencies (including `serde`, `serde_json`
and `sha2`); use `cargo fetch --locked` before offline tests. The
[public Rust workflow](.github/workflows/rust.yml) runs on pull requests,
pushes to `main`, and manual dispatch. Check the actual head SHA and run
conclusion; a previous green run is not evidence for a subsequent commit.

PR checks intentionally run on the submitted **head SHA**, not a synthetic
merge commit. Verify integration on the post-merge `main` SHA separately,
and never claim that a source-graph test fixture proves original Lean parity.

A green Rust workflow validates Rust formatting/tests/lints, **not** the
original Lean semantics, native TM2 refinement or the theorem. Original Lean
execution and mathematical resource accounting require separate evidence.

For a bug report, supply the affected commit, Rust toolchain, smallest
reproducing input (DIMACS when applicable), expected vs actual state/output,
and whether the failure occurs in the Rust port, original imported Lean, or
their comparison.

Original contributions use MIT. Adapted material from
[`openai/math`](https://github.com/openai/math) must preserve applicable
Apache-2.0 license notices and attribution.
