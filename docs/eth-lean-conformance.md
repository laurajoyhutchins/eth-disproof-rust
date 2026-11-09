# Lean implementation reference: precise correspondence boundary

Upstream source is pinned in [reference/lean_eth_source.json](../reference/lean_eth_source.json)
to commit **4eaee87548250b2682affda7d05d947c05554bae** of
[openai/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT).
The pin records each examined file's Git blob SHA and the actual upstream
toolchain, **Lean 4.34.1**. Updating the reference requires reviewing changes
and regenerating the differential fixtures, not silently following main.

## What the formalization actually constructs

[SqrtLogSpace/Final.lean](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean)
proves a single fixed primitive counting/SAT program for each width k >= 2.
The displayed program is BitProgram.Program 80 1220 labels, with count
output on stack 256 and SAT output on stack 1216. Its entry uses
Native.countingProgram cutoff k (NativeLeafProgram.command k).

The construction is defined by:
- NativeFrontend: explicit parsing and canonical normalization, with the
  declared Fin n variable universe preserved
- NativeOuter: concrete setup, disjoint counting DFS, complete-word output
- NativeLeafProgram: actual marked and accepted query programs
- FiniteFallback: an input-size cutoff and a **noncomputable** finite
  transition table, whose output definition uses SAT.count over finite
  formulas

The theorem supplies an existential cutoff and resource constants; this is
not a practical recipe for constructing the massive finite lookup table or
running the resulting primitive program.

## Implemented correspondence (finite definitions only)

| Lean source definition | Python implementation | Verification |
| --- | --- | --- |
| Encoding.encodeNat, frame, encodeList, literalCode, clauseNumbers, cnfNumbers, encodeCNF | eth/lean_wire.py | Fixed complete-bit golden vectors and an independent test-side encoder |
| SAT.removeTautologies; SAT.absorb; SAT.normalize | CNFFormula.__post_init__ | An independent finite-set specification, including tautologies, duplicate clauses and subsumption |
| DisjointBranch.selected, petals, negatedCoreUnits, childA, childB | eth/sparsification.py::_children | Independent set-model comparisons and pointwise disjoint/complete truth tables |
| DisjointBranch.count_children and declared Fin n | iter_disjoint_leaves | Exact per-assignment partition and ambient-variable retention on a finite case |
| SubexpNormalizationCorrectness.normalized_set | CNFFormula normal form | Set equality only; no primitive execution trace |

Run with:

    python -m pytest -q tests/eth/test_lean_source_conformance.py

The original 28 tests are **Python interpretations of explicit Lean
definitions**, not execution of Lean. They are now complemented by an opt-in
**real Lean 4.34.1 execution run**: a minimal pinned-Mathlib Lake overlay
imports the **unchanged upstream source files** at the exact revision. The
Lean source calls SAT.normalize, Encoding.encodeCNF, DisjointBranch.childA/B
and the **counting** SparseCountProgram.step/run; a separate Python process
compares every emitted encoded state and pointwise Boolean value.

Run the pinned GitHub workflow `.github/workflows/lean-source-trace.yml`
using workflow_dispatch or a branch `verify/lean-native-trace-*`. It builds
the actual imported ETH modules, **not** the complete upstream Lake project
and **not** the Final.lean primitive program. Its artifact retains the raw
Lean traces; a test failure refuses rather than silently substituting a
Python oracle.

**Important algorithm distinction exposed by execution:** The upstream
`ExecSparsifyWorklist` is a **satisfiability** worklist, which maintains
the union of satisfying assignments but not their disjointness. For
`(x1 OR x2) AND (x1 OR x3)`, its B-child is `x2 AND x3`, which overlaps
A's `x1` assignments (4 + 2 > 5). The counting branch in
`SqrtLogSpace/DisjointReuse/SparseCountProgram` instead constructs
`NOT x1 AND x2 AND x3`; its A/B counts are 4+1=5. The counting
program is the reference for all subsequent counting-DFS comparisons.
This difference is preserved as a fast negative regression.

## Important differences still unresolved

1. **Different algorithmic leaf.** Our eth/pipeline.py evaluates a bounded
   auxiliary spectral construction, certified Taylor coefficients and Hermite
   interpolation. It does *not* execute the concrete
   NativeLeafProgram.localCommand / marked-query / accepted-query machine.
   Its resource capacities and experimental r,Q,R choices are not the
   formalization's fixed-machine parameter schedule.
2. **Different input representation.** DIMACS is not Lean's CNF encoding.
   encode_lean_cnf translates normalized formulas to the exact binary
   encoding. Unnormalized Lean SAT.CNF sets can be imported by
   decode_lean_cnf, but normalization then changes their wire representation.
3. **Different normalization mechanism.** Python proves no primitive
   normalizedBody execution trace. The matching SAT.normalize clauses are
   only an extensional set-semantics check.
4. **Different finite fallback.** Our small active-variable case enumerates
   at most two assignments. Lean's small-input branch is a noncomputable,
   bounded-universe lookup table. Neither is an implementation of the other.
5. **Missing performance proof.** No Python resource ledger is a refinement
   of the machine's proven primitive-step or all-prefix visited-space bounds.

## Next executable refinement

Reproduce the pinned Lean 4.34.1/Mathlib build, start with the native
Encoding and normalization programs, and establish exact state-trace
correspondence on small formulas. Then examine disjoint DFS transition traces
and the NativeLeafProgram marked-query arithmetic.

Only after concrete instruction-level or functional refinement is established
should a Python optimization be described as implementing the formalized
machine. The finite exact-count agreement from Python's existing reference
pipeline is evidence of semantics, not of that refinement or of the
square-root-log time bound.
