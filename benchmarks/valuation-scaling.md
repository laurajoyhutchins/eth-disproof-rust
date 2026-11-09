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
`recursive-L4-p5` case runs the **complete 64-group four-slot,
one-active-level experimental contraction**. All three verify the root
result against independent direct two-wire contraction.

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
