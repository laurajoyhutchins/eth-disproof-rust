# Exact CNF counting, restricted affine instrument

This executable accepts standard DIMACS CNF and produces an exact model count
when **every** input clause belongs to the supported, strictly ordered grammar.
It reuses the packed affine elimination and independent dense replay checker in
the sibling Rust modules. There is **no general SAT solver fallback**.

From the repository root:

```sh
cargo test --manifest-path experiments/egg-contraction-optimizer/Cargo.toml
printf 'c equality and an unconstrained variable\np cnf 3 2\n1 -2 0\n-1 2 0\n' | cargo run --quiet --manifest-path experiments/egg-contraction-optimizer/Cargo.toml --bin exact-cnf-count -- -
printf 'p cnf 3 1\n1 2 3 0\n' | cargo run --quiet --manifest-path experiments/egg-contraction-optimizer/Cargo.toml --bin exact-cnf-count -- -
```

The first input has **4** satisfying assignments. The second input is refused
with exit status 2, even though a general SAT solver could count it.

## Accepted source syntax

* Standard `p cnf VARIABLES CLAUSES` header; signed integer literals and
  `0` terminators, including clauses spanning lines and comment lines.
* A unit clause expresses a fixed Boolean value; an empty clause is false.
* Two consecutive two-literal clauses may encode **one** XOR2 constraint,
  in the exact assignment-lexicographic canonical order:
  equality: `a -b 0` then `-a b 0`;
  inequality: `a b 0` then `-a -b 0`.
* Four consecutive three-literal clauses may encode **one** XOR3
  constraint. The variables must be distinct and ordered consistently
  across all clauses. The four clauses must block exactly the wrong-parity
  assignments in lexicographic order. Other arrangements are refused,
  even if logically equivalent.
* All declared variables, including unused variables, contribute to
  the model count. Recognized blocks can overlap in variables and be
  combined with units. Unsupported clause forms are **not** skipped.

The current recognizer is intentionally strict and is not a general XOR
extraction or arbitrary CNF compiler. The larger task is a source-normalized
factor network and a representation-aware composition planner.

## JSON receipts and limits

Success produces one JSON record on stdout, including the exact decimal
`count` (string), variables, clauses, recognized equation count, GF(2)
rank, free variables, row XORs, independent replay operation count, residual
rows and measured stage elapsed times in nanoseconds.

`packed_matrix_words` and `verifier_boolean_cells` are **structural
storage proxies**, not a whole-process memory bound. On Linux,
`process_peak_rss_kib` is measured from VmHWM for the whole process,
not attributed to a particular stage. Timing values are observations,
not an arithmetic or bit-complexity theorem.

Failure produces a JSON record on stderr with code, stage and detail, and
exits with status 2; stdout contains no purported count. Codes distinguish
invalid input, unsupported structure, resource refusal, and failed verification.

Configurable input guards:

```text
--max-input-bytes N   default 32000000
--max-variables N     default 100000
--max-clauses N       default 1000000
--max-literals N      default 4000000
```

The underlying affine producer and checker currently have additional
independent hard-coded matrix/transcript guards; their refusal is surfaced.
These guards should become configurable in a later shared resource policy.

## Correctness and research boundaries

The unit, empty, XOR2 and XOR3 encodings are independently tested by
brute-force Boolean CNF truth evaluation on small instances. The affine
producer returns row-operation transcripts replayed by an independently
implemented dense-Boolean checker. The count follows the rank/nullity
fiber formula already proved in Lean.

**What is not formally proved:** full DIMACS parser/recognizer refinement to
Lean; packed-Rust implementation correctness; machine bit-operation bounds,
peak space, general source-to-factor conversion, or closure under the OAI
QueryStream and Anthropic recursive operations. The kernel-checked Lean
theorems apply to the mathematical operations, not this whole executable.

For the mathematical background see the notebook pages on
[affine elimination](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/affine-elimination-certificates.md)
and [equality components](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/equality-component-contraction.md).

Next: preserve source-to-factor provenance, introduce boundary-aware region
planning, and measure interface size and coefficient growth across each
operation before attempting an end-to-end asymptotic claim.
