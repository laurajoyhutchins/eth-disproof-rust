# Exact valuation-scaling experiment

This experiment asks whether removing terms already known to vanish modulo
`2^p` saves real recursive work, rather than just mode catalog space.

`python -m benchmarks.valuation_scaling --repeats 2 --output artifacts/valuation-scaling.json`

The opt-in GitHub workflow on `verify/valuation-scaling-*` runs exactly
this command and retains the full report. Each arm is a **fresh Linux
process**, with a 768 MiB virtual-address limit and a 40-second per-run
timeout. An independent copy of the old `b+1` catalog supplies the control
arm; the other arm uses the current certified 2-adic valuation. No production
solver switch or runtime configuration is introduced.

The controlled experiments vary **padded** packet width `L=2,4,8,16`
and precision `p=5,7,9,11`, for exact two- and four-wire all-one networks.
Some slots are deliberately empty, so this does not imply growth in
occupied packet width. Both arms use exactly the same independently verified
deformation value and factorization strategy. The two `recursive-p5` and
`recursive-p7` cases run **the complete two-active-level micro-schedule
contraction**, including recovery and children. The
`recursive-L4-sparse-p5` case runs the **complete 64-group four-slot,
one-active-level experimental contraction** with separate pair-label classes.
All three verify the root result against independent direct two-wire
contraction. A distinct `recursive-L4-dense-p5` stress case places two
edges in one class, creates high-order modes and is **not** in the
default success matrix because both arms refuse the 4,096-state factor
limit. It can be reproduced explicitly with `--cases recursive-L4-dense-p5`;
that command must exit nonzero and retain `status=incomplete`.

Data distinguish (1) catalog descriptors, (2) mathematically admissible
weighted tuples from an independent polynomial-DP counter, and
(3) *actual* child evaluations, recursive calls, DP operations and factor
peaks. A small weighted domain is not by itself evidence that the solver
actually executes less work.

A capacity refusal, timeout or incorrect result is recorded as
`incomplete`; no comparative success, speedup or saved-work claim is
computed. All raw samples, statuses and counters are in the JSON artifact.
No asymptotic performance claim follows from these finite micro-schedules.
The literal paper schedule does not activate at these sizes.


## Verified finite results (2026-11-09)

[Fresh-process source-pinned run](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42690362967)
at `b99a8dbd3b27597e626098d1a00c275165b3fa5d`, Linux x86-64,
CPython 3.13.18, 768 MiB virtual-memory cap and two repetitions per arm.
Every row below completed and agreed with its independent exact oracle.
Counts are **per run**, rather than summing the repeated samples.

| Case | Modes old→pruned | Weighted assignments old→pruned | Actual child evaluations old→pruned |
| --- | ---: | ---: | ---: |
| center L2, p5, 2 wires | 2→2 | 4→4 | 8→8 |
| center L4, p5, 2 wires | 4→2 | 10→3 | 20→6 |
| center L4, p9, 2 wires | 8→6 | 44→11 | 88→22 |
| center L8, p7, 2 wires | 6→3 | 22→4 | 44→8 |
| center L8, p11, 2 wires | 10→7 | 82→12 | 164→24 |
| center L8, p11, 4 wires | 10→7 | 119→12 | 238→24 |
| center L16, p11, 4 wires | 10→6 | 119→8 | 238→16 |
| two-level micro recursion, p5 | 18→18 | 36→36 | 144→144 |
| two-level micro recursion, p7 | 18→18 | 36→36 | 144→144 |
| complete L4 sparse geometry64 recursion, p5 | 2→2 | 4→4 | 32→32 |

The center-only cases can save **actual recursive child evaluations**
even when no dense tensor is materialized. They are not end-to-end
interpolation/recovery benchmarks, and their wall-clock timings are
too short and few to establish a meaningful performance ratio.

The completed full recursion cases show **zero saved child evaluations**.
Their center precision is inflated to 133/261 (or 135/263) for the
two-level micro examples, and 245 for the L4 geometry64 case.
Every recorded catalog there has such a small exponent domain that its
**maximum possible** weighted degree is strictly below the precision.
Consequently every assignment fits in both arms and a stronger valuation
cannot remove any. The report now directly records this necessary
combinatorial saturation condition.

The independent dense L4 experiment at the prior implementation head
[run 42689796012](https://github.com/laurajoyhutchins/nonexp-sudoku/actions/runs/42689796012)
is a **capacity refusal, not a solver success**: 244 old versus 242
improved descriptors were constructed before both arms exceeded the
4,096-admissible-state limit on the first factor, with zero children
evaluated. It is retained as a separate opt-in stress case, rather
than silently folded into the completed matrix.

**Falsified for these test families:** that local valuation sharpening
alone materially reduces work in the first executable complete
recursions. In addition to mode sparsity, effective recursive
precision and factor-domain structure are decisive. This neither
disproves the published subexponential theorem nor extrapolates a
finite benchmark to an asymptotic claim.
