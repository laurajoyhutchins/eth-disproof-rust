# Lean proof style

These conventions apply to repository-authored `eth/proofs/*.lean` and
`instrumentation/lean-env/ACC/*.lean` modules. These are our own proof
obligations, not the source-pinned upstream modules.
They do not authorize editing the pinned upstream Lean sources or changing
an established theorem statement merely for appearance.

## Structure and names

- Start with imports, then a `/-! ... -/` module comment explaining the
  mathematical object, source assumptions, established result, and boundary.
- Use a namespace that describes the mathematical subject; close it explicitly.
  Keep existing public declaration names stable for downstream users.
- Document public results and nonobvious constructions with concise
  `/-- ... -/` comments. Describe what a definition denotes or what a
  theorem *proves*. Do not generate boilerplate for obvious local helpers.
  Put limitations beside the relevant result rather than in a generic
  disclaimer at the end.
- Use `/-! ## ... -/` headings for distinct stages in long developments.
  Prefer small named helper lemmas over a single long tactic search.
- Name hypotheses for their roles (`hinj`, `hcode`, `hfinite`); distinguish
  source objects, mathematical semantics, and implementation witnesses.

## Proofs and layout

- Indent tactic bodies two spaces and nested branches two further spaces.
  Prefer `exact`, `refine`, `calc`, and targeted rewriting when a
  small mathematical justification is available.
- Use `simp only` when the rewrite set is central to the argument; general
  `simp` and automation are fine when the result stays legible and checked.
  Do not rewrite working proofs just to replace one tactic with another.
- Introduce `classical` in the smallest convenient proof or definition.
  Make noncomputability explicit instead of masking a construction gap.
- Wrap lines at 100 characters or fewer, leave no trailing whitespace or tabs,
  separate top-level declarations with one blank line, and end with one newline.
- Group `#print axioms` checks at the end in declaration order where they
  exist. They complement, but do not replace, pinned kernel verification.

## Trust boundary

The style check is intentionally textual. It enforces formatting and module
documentation, and reports undocumented declarations as advisories by default
so already-open research branches are not blocked by a new editorial policy.
Use `--strict-docs` when deliberately auditing a fully documented module.
It checks **neither** elaboration, mathematical correctness, absence of
hidden axioms, nor source-to-Rust refinement. The original source-pinned
Lean workflows remain authoritative. Never replace a hard proof with `sorry`, `admit`, or an
unexamined axiom to make a style pass succeed.

Run the fast local check:

```sh
python3 tools/check_lean_proof_style.py
python3 -m unittest discover -s tools -p 'test_lean_proof_style.py'
```

Run the appropriate pinned Lean workflow whenever proof files change.
