# Pinned original Lean source

This branch is the **immutable upstream-source reference** for the literal Rust port maintained on `main`.

- Original repository: https://github.com/openai/math
- Exact source commit: `4eaee87548250b2682affda7d05d947c05554bae`
- Relevant source root: `upstream/openai-math/lean/OAI/Algorithms/SubexponentialSAT/`
- This is an upstream **Git submodule**, not a rewritten or translated source copy. OpenAI's upstream source and its licensing remain unchanged.

To inspect the source after checking out this branch:

```sh
git submodule update --init upstream/openai-math
```

A branch diff against Rust is **not** a completeness proof: filenames and symbol boundaries need not correspond one-to-one, and implementing a Lean definition does not imply Lean/Rust differential equivalence or preservation of primitive resource bounds. Track source symbols and coverage status in the Rust port separately: absent, stubbed, source-literal executable, tested against native Rust model, or directly checked against imported upstream Lean. Treat theorem obligations and full-machine behavior as independent tracks. Never erase upstream Lean definitions when ported.

The pin is intentional. To advance the upstream revision, create a separately reviewed provenance commit rather than silently following upstream HEAD.
