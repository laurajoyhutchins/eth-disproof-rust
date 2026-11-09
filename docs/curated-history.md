# Curated mathematical and engineering history

This branch is a **conceptual reconstruction** of the completed progress in `nonexp-sudoku`, not a reconstruction of how experiments happened in real time. The original PR discussions and source commits remain accessible on the historical `main` lineage. The original pre-PR concept commits and their smoke-test metadata remain in [HISTORY-MANIFEST.json](../HISTORY-MANIFEST.json).

**Original-main source pinned for reconciliation:** [`e5b4c376`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/e5b4c376a6a59bc0d524549d7cd354eb669fbdd9), including merged PRs through #82 on November 9, 2026. This reconstructed candidate additionally contains a source-boundary cleanup merged via [PR #80](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/80) into the curated branch, so its final tree is intentionally not identical to main.

## Read this history

The first nine synthetic milestones **point to exact Git trees of real merged mainline checkpoints**. Their SHA values, parents, and messages are new. A tenth milestone reconciles later original-main changes by importing their original blob SHAs into the cleaned tree. Because the reference-oracle extraction is retained, milestone 10 is **not** claimed to be identical to the original main tree. Separate documentation commits record this mapping.

| Phase | Curated commit | Corresponding main tree commit | Integrated work at that checkpoint | Interpretation |
| --- | --- | --- | --- | --- |
| 1. foundation | [`f711cc3c`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/f711cc3c9c921ae96b8e13ef1308a0f3bb0425ac) | [`916bd8e5`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/916bd8e52fba917bf39e12fd3f88c1db9d2c7128) | PR 1–3 | Structured identities, FLINT boundary, fast checkpoint |
| 2. budgets | [`8089d8b9`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/8089d8b9c45c7f8841025bc6af9c5529058440a6) | [`ad31d750`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/ad31d75081804abb75fb7486a626f8928a7739e0) | PR 4–6, 8–18 | Explicit resource budgets, local cost controls, paired evidence |
| 3. cnf | [`4816f044`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/4816f0449c2a63e765590400d0919a07cd850c80) | [`b89cbeef`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/b89cbeef9683ff1bdfeb664dd1610ca16fa252c2) | PR 7, 19–27 | Bounded end-to-end CNF counting and early structural obstructions |
| 4. measure | [`822eefc9`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/822eefc91ae7f8359574e670aa59dcb6bc18aca3) | [`6c9024b4`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/6c9024b435b19ace0ff9c3a4d5b26d108f3867f4) | PR 28–38 | Native verification, factor saturation, source-pinned Lean traces |
| 5. algorithms | [`6d190198`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/6d1901980ac879619425b8f80dc5de1436c7d3a6) | [`ce3e036e`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/ce3e036e1f7d1ecceb93c3481cd2280a377e8347) | PR 39–47 | Certified Sudoku oracles and multiple exact Taylor evaluators |
| 6. support | [`24d2c4ef`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/24d2c4ef4213a10262677c236514680937f45b71) | [`b82c5d0a`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/b82c5d0a2bbada23320c936e58b6b551388209f2) | PR 50, 53–57 | Packet support, rank and sparse-multilinear comparisons |
| 7. theorem | [`2fd502ad`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/2fd502adab75d3d2cf359586b8859a2bd26370a8) | [`7a599d0c`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/7a599d0c7b96b7f5fc41455eca69cdee8921e103) | PR 58–63 | Pure elimination planner, conditional whole-frame work and RED theorem gate |
| 8. frontier | [`07abea94`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/07abea94ace2f0f7b354e1002ba5b3572c6788da) | [`de3fc95b`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/de3fc95b986ab5f1a20d0c5cc25a22847993e021) | PR 51, 65, 67–70 | Total exponential #SAT baseline, transfer obstruction, all-center rank |
| 9. local proof | [`411ca927`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/411ca927a0b09eff82a9a962c510535af6567319) | [`d5319038`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/d53190383fbf7a4f97e576c8b3a8db75c4f30155) | PRs 71, 73, 75 | Local Lean verification, selective checkpoint planning and bounded target-coefficient research |

| 10. reconciliation | [`577214c7`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/577214c7a8eb02f33c1173ff45be8456d08d53d8) | [`e5b4c376`](https://github.com/laurajoyhutchins/nonexp-sudoku/commit/e5b4c376a6a59bc0d524549d7cd354eb669fbdd9) | PRs 72, 76, 79, 82 | Import original mathematical work without undoing the reference-only Sudoku oracle cleanup |

The PR-number descriptions indicate the major merged work completed in each *chronological interval*. They are not exhaustive patch ownership or a guarantee that all those PRs can be cherry-picked independently. The nine source-identical milestone trees and the tenth independently reconciled tree are intentional. Phase 10 preserves the cleaned runtime/ref boundary, while importing source blobs from the pinned merged-main snapshot. No unknown mathematical patch was reconstructed from inference.

## What is supported

- **Correctness:** Sudoku and CNF encodings, several bounded exact counting algorithms, exact coefficient and tensor arithmetic, conditional decomposition and certified symmetries have differential or independent-oracle tests for their declared domains. Capacity refusal is not an exact answer.
- **Performance:** Native Cython and FLINT are optional accelerators, kept where mathematical equivalence and paired performance evidence justify them. A faster kernel is not an asymptotic result.
- **Known mathematics:** Local mode, packet, rank and support bounds are conditional on explicitly stated representations and source behavior. In particular, the separate total exact CNF reference has an explicit **exponential** bit-work bound; the current conditional Sudoku-cell transfer does not prove `2^{o(N)}`.
- **Missing theorem:** `research_acceptance/test_complete_bit_recurrence.py` remains intentionally RED. No non-refusing, subexponential worst-case bit-complexity proof for generalized Sudoku is established.

Start with [system map](system-map.md), then [claims](claims.md) and [complete theorem acceptance](complete-theorem-acceptance.md). Use `git log --reverse --oneline` to read the conceptual stages.

## What was deliberately not imported

Work outside the pinned **merged** source head is not quietly promoted into the clean slate. At this snapshot this includes:
- [#48](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/48): pre-factor zero-support scheduling experiment
- [#49](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/49): deeper native Lean BitProgram traces
- [#52](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/52): draft bibliography
- [#66](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/66): restricted OR-clique quotient
- [#74](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/74): preconstruction target-degree pruning
- [#64](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/64): one-off planner A/B benchmark, closed without merge; its regression diagnosis was addressed by [#68](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/68)

These are *excluded from the snapshot*, not deleted from GitHub. The source contains opt-in `reference/`, `benchmarks/`, and `eth/` research algorithms that should remain visibly distinct from default runtime choices. Deleting historically merged implementations without dependency analysis and differential testing would manufacture a clean-looking but unreliable codebase.

## Production and independent reference boundary

[PR #80](https://github.com/laurajoyhutchins/nonexp-sudoku/pull/80) moved the exhaustive Cauchy deformation evaluator and synthetic micrograph from `sudoku/encoding.py` to `reference/sudoku_network_oracle.py`. The runtime adapter now imports only finite Sudoku input-oracle and graph types. Existing reference/benchmark consumers were updated, and the checkpoint contains a boundary regression test. This is a structural separation, not a new solver or a complexity improvement.

## Promotion and preservation

1. Preserve original history under [`archive/pre-clean-slate-20261109`](https://github.com/laurajoyhutchins/nonexp-sudoku/tree/archive/pre-clean-slate-20261109) and reconcile that archive with any new merges before cutover.
2. Run strict mypy, pure checkpoint, end-to-end exact counts, independent-oracle comparisons, and opt-in native parity at this exact tip. Do not put Lean/Mathlib on hot CI.
3. Inventory any remaining superseded adapters, aliases, dead workflows and shadow implementations; remove each only with a reference-oracle test and a demonstrable consumer migration. Do not drop negative witnesses or intentionally RED theorem acceptance.
4. Reconcile commits merged into historical `main` after the pinned source head; never assume the snapshot is live current main.
5. Promotion of this graph to `main` is a **history replacement**, not an ordinary pull-request merge. Use a protected backup and an explicit, leased ref update only after owner approval.

**Verification distinction:** Nine original-snapshot tree identities are structural evidence. The source-boundary move passed strict mypy and the pure-Python checkpoint at PR #80 (1,022 passed, 170 skipped, 464 deselected); optional native/FLINT/Ganak and full integration tiers were not rerun by the synthetic history operation. The reconciled branch tip requires new exact-head verification.
