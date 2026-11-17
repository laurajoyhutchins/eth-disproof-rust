# M2 #108: finite-fallback decision and support boundary

Source pin: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.
Source file: `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FiniteFallback.lean`,
blob `1fc8e1817b4f24d3255ef8fc398fb2127d214284`. The same pin is
already recorded in `reference/source-manifest.json`.

## Decision: refuse bounded counting until its table is justified

The finite scanner and cutoff comparison **are constructive**. The finite
SAT counting table in the pinned Lean file is not: `inputBound`,
`tableCount`, `outputTable` and the `Fintype.equivFin`-selected
`countProgram` are used under noncomputability. No concrete table of
labels, state mapping and full binary output words is supplied by Lean
as executable data. In particular, substituting a Rust truth-table SAT
oracle at runtime would not port this bounded finite-control program.

The Rust boundary remains:
- `finite_fallback::cutoff_scanner(cutoff)` creates the source-defined
  saturated true-bit scanner, up to a documented static table allocation cap.
- `finite_fallback::cutoff_command(cutoff)` runs the physical 80×1220
  cutoff command: preserved source header stack 258; cleared work 270
  and scratch 271; register map 72/73 for copy and 75/76 for the flag.
- `remaining::outer::cutoff_scan` exposes this executable stage.
- `remaining::outer::finite_fallback` and `remaining::outer::entry`
  **return `Error::NotImplemented` for every input**, regardless of the
  cutoff or large-branch command supplied. They are not executable counting
  operations. They may not be treated as returning zero or an answer.

The full source definition is
`FiniteFallback.dispatchCommand B large :=
  seq (cutoffCommand B) (ite 75 (framedCommand B) large)`.
The `n ≤ B` branch relies on `countProgram B`; the `n > B` branch
calls the supplied large machine after the cutoff. As the Rust outer
branch is unfinished, this increment does not enable either complete
entry branch.

## Bounded source domain and expected table contract

`SmallFormula B` contains each `n : Fin (B+1)` and all
`SAT.CNF (Fin n)`; this includes empty clauses and unused ambient
variables. Input keys are **canonical** `Encoding.encodeCNF` bit words,
not DIMACS. The source bound is the maximum length of those keys;
out-of-range overlong scanner prefixes reach the single overflow state.
For a complete key the source table emits `countWord (SAT.count F)`
(the full binary count, not just satisfiability), and for invalid or
overflowing keys its fallback output is `[false]`. Every output is
chosen in the *fixed transition table before runtime input*. An
equivalent Rust construction would need a reproducible enumeration
and exact output word for every finite state, including the states'
label ordering and all associated program instructions; a different
finite control may be observationally equivalent, but is not
definitionally the same Lean-selected `Fintype.equivFin` witness.

## Validation and remaining obligations

The scanner increment tests all bit words up to length eight for
cutoffs zero through six, both sides of the comparison, dirty scratch
cleanup, protected frames, exact source instruction counts and bounded
runtime/table refusals. The executable Rust scanner has a deterministic
state-major label enumeration, a bijective renaming of the source
`Fin (B+2) × Fin 7` labels. These tests are Rust-only and do not
establish original imported Lean trace parity.

To replace the refusal later, independently generate and pin the
entire finite table for a fixed supported cutoff with its upstream
source revision, enumerate small formulas with ambient variable
multiplicity preserved, check all output words with a separate exact
truth-table oracle, construct and test a physical fixed table (not a
runtime SAT enumerator), and prove or explicitly qualify observational
equivalence to Lean. The exact Lean-selected label enumeration is
noncomputable, so any claimed structural identity requires extra
justification. Until then, retain `Status::Noncomputable` for
`finite_fallback`. The native M2 high-query/leaf/DFS counting chain
(#105, #106, #107) additionally requires the unfinished M1 query stream
(#104). No primitive TM2 or ETH complexity claim follows.
