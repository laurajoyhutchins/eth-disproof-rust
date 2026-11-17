# Remaining source-defined execution path

**Current source of truth:** [`src/remaining.rs`](../src/remaining.rs)
declares the ordered executable dependency spine and exact Lean symbols.
[`reference/source-manifest.json`](../reference/source-manifest.json) pins
the upstream `openai/math@4eaee87548250b2682affda7d05d947c05554bae`
source identity. Neither a registry entry nor a hash proves equivalence.

Do not treat this document as a second, manually maintained stage-status
database. The registry is checked for unique names, ordered prerequisites,
machine boundaries and missing source pins by Rust tests. A stage marked
`Executable` means Rust code is exercised; it does **not** mean its original
Lean implementation has been independently run and compared.

## Completed boundary on `main`

The canonical DIMACS-to-bitword interface and the finite machine
`Native.frontendCommand` are runnable in Rust. See
[`eth-frontend`](../src/bin/eth-frontend.rs) and the
[frontend specification](m2-runnable-frontend.md). The 80-register,
1,220-stack frontend parses the header, normalizes the clause body and
restores its designated ABI ports. It does not return a satisfying-assignment
count; answer stack 263 remains empty.

Selected high/count seed, cache, head, tuple, pair, normalization and terminal
components are also executable as **fragments**. Their existence does not
turn `QueryStreamProgram.command` or `Native.countingProgram` into a
complete native path.

## Missing dependencies, in order of significance

1. **One real query:** finish the source-defined
   `QueryStreamProgram.command`, including signature-head loading/visiting,
   pair commitment, node append and count reconstruction. A host query
   calculator or fixture is not a replacement.
2. **High-query and leaf execution:** run the original high-query
   prepare/marked/accepted paths, `NativeLeafPreparation.command`,
   source-defined leaf rounds and accepted-query callback.
3. **Native count:** compose the real leaf with disjoint
   `DFSCountProgram.command` and `Native.outerCommand` through
   `Native.countingProgram`. First demonstrate **one nonterminal CNF** on
   the actual instruction machine, independently checking its count.
4. **Fallback:** the Lean finite fallback uses a noncomputably selected
   table. Deriving a bounded explicit table is a separate project requiring
   source semantics and table-generation checks, not permission to invoke
   the crate's exponential enumeration oracle silently.
5. **Formal resource evidence:** independently execute the pinned Lean
   source to compare machine states/transitions/halting, then separately
   establish primitive `BitProgram.tm` and
   `GuardedCompiler.primitive` TM2 correspondence and resource bounds.

The final theorem in `SqrtLogSpace/Final.lean` remains a mathematical
proof obligation, **not** a Rust function returning a Boolean.

## Failure and evidence policy

Unavailable constructors must fail with `Error::NotImplemented` rather
than fabricate a halt, empty program, zero answer or successful count.
Where the registry still denotes `Partial`, verify the actual runnable
prefix/suffix before calling it from a larger program.

Use [the central evidence matrix](evidence.md) to determine the level of
verification currently accepted on `main`; use the original Lean source and
the typed Rust registry when implementing the next dependency. Tests in
`tests/remaining.rs` and `tests/remaining_tdd.rs` enforce graph boundaries
and refusal behavior, but are not a substitute for actual source execution.
