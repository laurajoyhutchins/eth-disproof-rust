# Lean-to-Rust semantic correspondence

The compiler work has two independent acceptance targets.

**G1:** Compile ordinary executable Lean declarations to Rust, with the original runtime semantics.

**G2:** Compile the actual ETH counting program, including the parts of the Lean source that do not have ordinary compiler IR.

Passing G1 does not establish G2. The original `SqrtLogSpace.QueryStreamProgram.program` appears inside a `noncomputable section`; compiler-IR extraction does not automatically yield an executable version.

## G1: executable declarations and runtime semantics

A generated Rust program must match the original Lean program, including relevant runtime behavior. Tests of independently hand-written Rust are insufficient.

| Source feature | What can go wrong |
| --- | --- |
| Constructors and cases | `Option`, `List`, `Sum` and custom inductives reuse tags; the family identity matters |
| Mixed object/scalar fields | `sproj(n, offset, x)` addresses scalar bytes after \(n\) pointer fields. It is not `proj(i,x)` |
| Arrays and sharing | An aliased `Rc` value cannot be mutated as though it were uniquely owned |
| Closures and effects | Erased values, first-class functions, sharing observations and side effects need source-accurate behavior |
| Transitive closure | A supported entrypoint is useless if one called declaration silently disappears |

The intended implementation has **one** in-process Lean 4.34.1 compiler and one GMP/`Rc` value runtime. Do not maintain a second hand-translated object model.

Merged [#230](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/230) and [#234](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/234) are historical integration points. The November 14 follow-ups [#237](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/237), [#238](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/238) and [#239](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/239) record the scalar-projection and ownership issues. Their descriptions are not substitutes for checking the current head.

G1 acceptance requires **three substantial, unchanged external Lean programs**: original Lean execution, source-IR capture, generated Rust execution, and independent output/state agreement. Compiler-generated fixtures alone do not count.

## G2: noncomputable ETH declarations

The target sequence is

```text
QueryStreamProgram.command
  → native high query
  → native leaf
  → DFSCountProgram.command
  → Native.outerCommand
  → Native.countingProgram
```

The query path needs signature-head loading, pair commitment, node processing and count reconstruction. Partial source graphs do not imply the composite graph.

For a source declaration without executable IR, inspect its elaborated Lean `Expr` definition. A residualizer must preserve binding, sharing, reduction and dependencies. It must refuse computational axioms, unknown opaque constants, unresolved recursors or exhausted budgets. It cannot replace them with a plausible Rust #SAT algorithm.

The [compiler-IR probe](../rust/lean_eth_reference/docs/compiler-ir-backend.md), [core-expression residualizer](../rust/lean_eth_reference/docs/core-expr-residualizer.md) and [shared receipt contract](../rust/lean_eth_reference/docs/two-path-acceptance-contract.md) explore these boundaries. None establishes the full ETH program by itself.

The original query/composition drafts are [#177](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/177) and [#179](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/179).

## Correspondence obligations

```text
pinned Lean declaration
          ↓
actual IR or justified residualization
          ↓
source-equivalent BitProgram
          ↓
same physical instructions, labels and ports
          ↓
independently matched Lean/Rust state traces
          ↓
primitive TM2 time and visited-space bound
```

Source Git blobs, Mathlib and compiler pins belong in the certificate. Every unsupported construct must have a reason attached.

[PR #178](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/178) established a formal identity bridge **conditional on complete physical graph agreement**. It does not establish that Rust produced the missing full graph. Matching final counts also does not prove matching states, instruction costs or tape use.

## Finite fallback

The Lean finite branch uses a noncomputably selected table. A Rust exhaustive search is not a compilation of that table.

The available outcomes are construction and certification of the exact table, or an explicit refusal for the unsupported branch. The separate bounded #SAT oracle is for differential testing, never a silent runtime fallback.

See [finite fallback](../rust/lean_eth_reference/docs/m2-finite-fallback-decision.md).

## Completion criteria

Run one **nonterminal** instance through the complete original-source query, leaf, DFS and outer machine. Compare original Lean and generated Rust at each physical step: program counter, registers, stacks, output, halt and refusal. Bind the result to source SHAs, toolchains, emitted artifact hashes and the exact CI head. Then prove the primitive resource transfer.

Additional isolated fixtures do not substitute for this complete-program acceptance test.

[Current execution evidence](../rust/lean_eth_reference/docs/evidence.md) · [Remaining port](../rust/lean_eth_reference/docs/remaining-lean-port.md)
