# Lean → Rust compilation: G1/G2 semantics and remaining acceptance

**Snapshot:** 14 November 2026. Scope is the source-pinned ETH construction, not a generic compiler maturity claim.

## Two gates with different meanings

- **G1, ordinary executable Lean:** compile a *real* declaration's transitive compiler-IR closure into a standalone Rust artifact. Match original Lean semantics for Nat/Int, constructed objects, exact constructors/cases, closures, sharing/ownership and supported effects. Accept three substantial unchanged external Lean programs, not merely compiler-generated fixtures.
- **G2, original noncomputable ETH closure:** compile the source-defined `SqrtLogSpace.QueryStreamProgram.program` and its real high-query/leaf/DFS/outer composition. Ordinary compiler IR extraction does not make a declaration inside a `noncomputable section` executable. Source-preserving symbolic residualization is required; if unavailable it must refuse.

Both gates need a common, exact source identity and independent semantic agreement. G1 success does not imply G2 success.

## Fixed sources and runtimes

- Upstream ETH source: [openai/math@4eaee87548250b2682affda7d05d947c05554bae](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT), tracked by [manifest](../rust/lean_eth_reference/reference/source-manifest.json).
- Original Lean: **4.34.1**. Rust workspace: **1.99.1**, from [toolchain](../rust-toolchain.toml). External leanfran smoke work used Lean 4.35.0 and therefore cannot silently stand in for the original source/toolchain.
- The preferred G1 implementation is the **single in-process compiler and canonical GMP/Rc runtime**, rather than competing JSON-IR transports and duplicate object/Nat runtimes. [Merged #230](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/230) supplied source-exact List constructor cases; [merged #234](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/234) reconciled Array and external source work. Inspect the exact main head and independent CI receipts before relying on numerical fixture totals.

## Open semantic corners, anchored to concrete PRs

| Area | Failure mode | Acceptance |
| --- | --- | --- |
| Inductive representation | Tag/object identity conflated across Option, List, Sum or user constructors | Source CtorInfo family, tag and pointer/scalar field layout agree, otherwise refuse. [#239](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/239), open |
| Object and scalar fields | Treating scalar `sproj(n,offset,x)` as ordinary object `proj(i,x)` changes field meaning | Capture actual Lean IR for mixed Bool/Nat/Option structure, match scalar byte offset after pointer fields, validate `proj` and `uproj`; [#237](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/237), [#238](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/238), open |
| Mutable/persistent Array | A shared `Rc` alias cannot be mutated as though uniquely owned | Source-defined persistent behavior or verified last-use uniqueness; compare pointer identity, aliasing and values; [#239](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/239) |
| Functions and effects | Callable objects, closures, erased proofs, sharing observations and effects differ from Lean runtime | Exact source-IR closure, no speculative externs, side-effect and ownership oracles, explicit refusals for unsupported constructs |
| G1 external acceptance | A generated fixture is not an unchanged project | Pin external repo, build exact original Lean, compile untouched exported declaration, independently compare outputs and full tested behavior |
| G2 symbolic source | Noncomputable definition lacks ordinary executable IR | Traverse elaborated original Lean `Expr` DAG, preserve sharing and finite reductions, prove each reduction; refuse opaque computational dependencies, unresolved recursors and exhausted budgets |
| Query machine | Partial source fragments have incompatible labels/ports or do not compose | Complete original `QueryStreamProgram.command`: head loading, pair commitment, node visiting, count reconstruction; source-backed physical instruction graph; [#177](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/177) still draft |
| Native count | High/leaf/DFS/outer exist individually but not together | One source-generated program, real nonterminal count and original-Lean differential; [#179](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/179) still draft |

The [generic compiler-IR probe](../rust/lean_eth_reference/docs/compiler-ir-backend.md), [symbolic core residualizer](../rust/lean_eth_reference/docs/core-expr-residualizer.md), and [two-path receipt contract](../rust/lean_eth_reference/docs/two-path-acceptance-contract.md) are separate experiments. The desired direction is a single source-semantics contract with explicit applicability, not two mutually substitutable algorithms.

## Formal refinement ladder

1. **Source identity:** Git blob hashes, toolchains, Mathlib commit, original `Lean.Name`, exact declaration roots, compiler version and all transitive computational dependencies are recorded.
2. **Lean declaration semantics:** identify actual compiler IR, or a kernel-justified residualized expression path. Unsupported source terms are refused.
3. **BitProgram identity:** entry/exit labels, physical instructions, all ports, call relocations, original stack/register ABI and halting behavior agree with the pinned original Lean graph.
4. **Independent execution:** original Lean and generated Rust produce equal bounded *full-state* traces, not just equal final counts. Include negative, malformed, sharing, overflow and resource-bound cases.
5. **Abstract primitive-machine bridge:** [merged PR #178](https://github.com/laurajoyhutchins/eth-disproof-rust/pull/178) proves that a completely identical source physical graph transfers to the same formal Lean primitive TM2 machine. This does **not** prove that Rust emitted/executed the missing complete graph.
6. **Final theorem connection:** prove the actual complete native source counter and its primitive time/visited-space bound. Rust wall clock, allocations, or BitProgram instructions are not the TM2 bound.

No level can be inferred solely from the evidence of another.

## Noncomputable small-input branch

The original Lean cutoff uses a *noncomputably selected finite table*. Implementing brute force at runtime is **not** compilation of that branch. The correct runtime policy is source-refined fixed table with independently certified construction, or **unsupported**. A mathematically permitted large-input path may be used only after its entire source-defined counting program is compiled and verified; it cannot be inferred from the nominal cutoff alone. See [finite fallback disposition](../rust/lean_eth_reference/docs/m2-finite-fallback-decision.md).

## Reproducible acceptance record

For each candidate, retain:

- Immutable source Git revision and file blobs; Lean/Mathlib/Rust versions and Cargo lock hash.
- Exact compiler and runtime commits, declared G1/G2 coverage, full refusal ledger and artifact SHA-256.
- Original Lean command and all original-source test oracles; separate generated Rust command.
- Per-input source and Rust result, trace hash, first divergent state if any, machine step/stack counts, bit operations and peak bytes.
- Exact-head CI check id and external reproducibility instructions; cached artifacts only when their entire identity contract matches.

The authoritative existing [execution matrix](../rust/lean_eth_reference/docs/evidence.md) remains the mainline truth. Do not overwrite it with aspirational counts from this note.
