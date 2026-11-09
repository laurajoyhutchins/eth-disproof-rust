# Curated mathematical and engineering history

This branch is a **conceptual reconstruction** of the completed progress in `nonexp-sudoku`, not a reconstruction of how experiments happened in real time. The original PR discussions and source commits remain accessible on the historical `main` lineage. The original pre-PR concept commits and their smoke-test metadata remain in [HISTORY-MANIFEST.json](../HISTORY-MANIFEST.json).

**Pinned source:** [`d5319038`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/d53190383fbf7a4f97e576c8b3a8db75c4f30155), merged through PR #75 on November 9, 2026. This is a deliberately fixed integration snapshot; other branches may advance afterward.

## Read this history

Each of the nine synthetic commits **points to the exact Git tree of a real merged mainline checkpoint**, then names the mathematical/engineering theme and its limitations. Consequently the nine intermediate trees are source-identical to historic states. Their individual SHA values, parents, and commit messages are new. The **tenth, documentation-only commit** repairs the navigation and history manifest; it does not claim to improve the algorithms.

| Phase | Curated commit | Corresponding main tree commit | Integrated work at that checkpoint | Interpretation |
| --- | --- | --- | --- | --- |
| 1. foundation | [`f711cc3c`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/f711cc3c9c921ae96b8e13ef1308a0f3bb0425ac) | [`916bd8e5`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/916bd8e52fba917bf39e12fd3f88c1db9d2c7128) | PR 1–3 | Structured identities, FLINT boundary, fast checkpoint |
| 2. budgets | [`8089d8b9`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/8089d8b9c45c7f8841025bc6af9c5529058440a6) | [`ad31d750`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/ad31d75081804abb75fb7486a626f8928a7739e0) | PR 4–6, 8–18 | Explicit resource budgets, local cost controls, paired evidence |
| 3. cnf | [`4816f044`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/4816f0449c2a63e765590400d0919a07cd850c80) | [`b89cbeef`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/b89cbeef9683ff1bdfeb664dd1610ca16fa252c2) | PR 7, 19–27 | Bounded end-to-end CNF counting and early structural obstructions |
| 4. measure | [`822eefc9`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/822eefc91ae7f8359574e670aa59dcb6bc18aca3) | [`6c9024b4`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/6c9024b435b19ace0ff9c3a4d5b26d108f3867f4) | PR 28–38 | Native verification, factor saturation, source-pinned Lean traces |
| 5. algorithms | [`6d190198`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/6d1901980ac879619425b8f80dc5de1436c7d3a6) | [`ce3e036e`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/ce3e036e1f7d1ecceb93c3481cd2280a377e8347) | PR 39–47 | Certified Sudoku oracles and multiple exact Taylor evaluators |
| 6. support | [`24d2c4ef`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/24d2c4ef4213a10262677c236514680937f45b71) | [`b82c5d0a`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/b82c5d0a2bbada23320c936e58b6b551388209f2) | PR 50, 53–57 | Packet support, rank and sparse-multilinear comparisons |
| 7. theorem | [`2fd502ad`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/2fd502adab75d3d2cf359586b8859a2bd26370a8) | [`7a599d0c`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/7a599d0c7b96b7f5fc41455eca69cdee8921e103) | PR 58–63 | Pure elimination planner, conditional whole-frame work and RED theorem gate |
| 8. frontier | [`07abea94`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/07abea94ace2f0f7b354e1002ba5b3572c6788da) | [`de3fc95b`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/d53190383fbf7a4f97e576c8b3a8db75c4f30155) | PR 51, 65, 67–70 | Total exponential #SAT baseline, transfer obstruction, all-center rank |

| 9. local proof | [`411ca927`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/411ca927a0b09eff82a9a962c510535af6567319) | [`d5319038`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/d53190383fbf7a4f97e576c8b3a8db75c4f30155) | PRs 71, 73, 75 | Local Lean verification, selective checkpoint planning and bounded target-coefficient research |

The PR-number descriptions indicate the major merged work completed in each *chronological interval*. They are not exhaustive patch ownership or a guarantee that all those PRs can be cherry-picked independently. The real intermediate Git trees, rather than reconstructed partial patches, are intentional: no synthetic state is fabricated merely for a prettier log.

## What is supported

- **Correctness:** Sudoku and CNF encodings, several bounded exact counting algorithms, exact coefficient and tensor arithmetic, conditional decomposition and certified symmetries have differential or independent-oracle tests for their declared domains. Capacity refusal is not an exact answer.
- **Performance:** Native Cython and FLINT are optional accelerators, kept where mathematical equivalence and paired performance evidence justify them. A faster kernel is not an asymptotic result.
- **Known mathematics:** Local mode, packet, rank and support bounds are conditional on explicitly stated representations and source behavior. In particular, the separate total exact CNF reference has an explicit **exponential** bit-work bound; the current conditional Sudoku-cell transfer does not prove `2^{o(N)}).
- **Missing theorem:** `research_acceptance/test_complete_bit_recurrence.py` remains intentionally RED. No non-refusing, subexponential worst-case bit-complexity proof for generalized Sudoku is established.

Start with [system map](system-map.md), then [claims](claims.md) and [complete theorem acceptance](complete-theorem-acceptance.md). Use `git log --reverse --oneline` to read the conceptual stages.

## What was deliberately not imported

Work outside the pinned **merged** source head is not quietly promoted into the clean slate. At this snapshot this includes:
- [#48](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/48): pre-factor zero-support scheduling experiment
- [#49](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/49): deeper native Lean BitProgram traces
- [#52](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/52): draft bibliography
- [#66](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/66): restricted OR-clique quotient
- [#72](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/72): universal deformation bit-height proposal
- [#74](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/74): preconstruction target-degree pruning
- [#64](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/64): one-off planner A/B benchmark, closed without merge; its regression diagnosis was addressed by [#68](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/68)

These are *excluded from the snapshot*, not deleted from GitHub. The source contains opt-in `reference/`, `benchmarks/`, and `eth/` research algorithms that should remain visibly distinct from default runtime choices. Deleting historically merged implementations without dependency analysis and differential testing would manufacture a clean-looking but unreliable codebase.

## Promotion and preservation

1. Keep the historical `main` commit and every original PR accessible under a permanent archive branch or tag **before** replacing the default branch.
2. Run strict mypy, pure checkpoint, end-to-end exact counts, independent-oracle comparisons, and opt-in native parity at this exact tip. Do not put Lean/Mathlib on hot CI.
3. Inventory any remaining superseded adapters, aliases, dead workflows and shadow implementations; remove each only with a reference-oracle test and a demonstrable consumer migration. Do not drop negative witnesses or intentionally RED theorem acceptance.
4. Reconcile commits merged into historical `main` after the pinned source head; never assume the snapshot is live current main.
5. Promotion of this graph to `main` is a **history replacement**, not an ordinary pull-request merge. Use a protected backup and an explicit, leased ref update only after owner approval.

**Verification distinction:** Tree identity with each recorded original snapshot is structural evidence; no new whole-repository test run has been performed merely by creating these Git commits.
