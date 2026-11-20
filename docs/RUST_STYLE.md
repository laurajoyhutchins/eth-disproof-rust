# Rust code conventions

These conventions apply to locally maintained Rust in `eth/` and
`compiler/`. The original pinned Lean sources and recorded source identities
are not style-refactoring targets. Formatting and Clippy are necessary checks,
not proof of behavioral equivalence.

## Organization

- Organize by responsibility: `bit_program` is the finite machine,
  `machine` is normalization, `query` is source query execution,
  `counting` is counting and resource audits, and `compiler` is the
  independent Lean-IR backend. Do not create another code-generation path.
- Order imports in separate standard-library, external-crate, and local-module
  groups. Prefer explicit imports to glob imports except for stable compatibility
  re-exports.
- Use `snake_case` for functions, fields, and modules; `CamelCase` for types.
  Preserve public/source-linked names where changing them would invalidate
  evidence or compatibility. Prefer descriptive locals such as `audit`,
  `state`, `program`, and `limits` over context-free single letters.
- Put a short `//!` header on each source-translation module identifying what
  it implements and what remains outside its execution boundary. Use `///`
  for public contracts and `//` for local invariants. State facts once;
  avoid repeating a paragraph of qualifications on every function.
- Keep the source `StackRoutines.clearProgram`, `copyProgram`, and
  `transferProgram` label tables in `bit_program/stack_routines.rs`. Use
  compatibility re-exports rather than copying instruction tables into
  normalization, query, or counting modules.
- Extract a helper when distinct callers share a genuine representation
  contract. Keep diagnostic-only helpers in the diagnostic surface, rather
  than exposing them as library APIs or duplicating them in each binary.

## Source and execution boundaries

- Refer to a pinned Lean declaration precisely; distinguish source commands,
  Rust adapters, tests, and independent mathematical statements.
- Use `Result` and checked arithmetic for untrusted input and bounded
  resources. Do not convert unsupported stages into zero counts or successful
  halts. Keep `Error::Invalid`, `Error::Capacity`, `Error::Overflow`,
  and `Error::NotImplemented` semantically distinct.
- Keep serialized field names, bit ordering, physical register/stack indices,
  refusal statuses, and CLI exit codes stable unless a separately tested
  protocol change is intended. In particular, the `appendix-*` programs
  print arithmetic receipts but always exit **2**, including when an audit
  finishes normally. Their common convention is `run() -> Result<(), String>`
  followed by one small refusal-printing `main()`.
- Build JSON receipts with unique keys. A repeated key in a `json!({ ... })`
  expression is especially easy to overlook in review.
- Keep format-only changes and helper extraction separate from math,
  performance, and semantics changes. A rustfmt-clean diff is not a Rust/Lean
  correspondence theorem.

## Evidence for a refactor

1. Identify the observable contract: field names and JSON values, exact trace
   bytes, exit code and stderr, machine steps, and resource refusals.
2. Compare before and after on the same fixtures; add an independent test for a
   shared helper or a nontrivial transformation. Do not bless a rewritten
   producer as its own oracle.
3. Run `cargo fmt --all -- --check`,
   `cargo test --locked --offline --all-targets`, and
   `cargo clippy --locked --offline --all-targets -- -D warnings` at
   the repository root. Compiler CLI gates are separate and documented in
   `CONTRIBUTING.md`.
4. Record checks against the exact changed head. A passing Rust test does not
   verify the original Lean program or the complexity theorem.

See [the contribution contract](CONTRIBUTING.md) and
[the evidence stages](https://github.com/laurajoyhutchins/eth-disproof-rust/blob/main/AGENTS.md).
