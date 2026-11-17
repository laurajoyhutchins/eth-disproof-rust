# M2 complete source-native normalization, with native ABI lift

**Upstream reference:** `openai/math@4eaee87548250b2682affda7d05d947c05554bae`, using original Lean 4.34.1 finite BitProgram instructions. No Rust-host normalization, subset oracle or semantic clause filtering is used by the **production machine code**. Independent predicates appear only in tests.

## Original physical program chain

| Source-defined stage | Rust implementation and bank | Function |
| --- | --- | --- |
| `ExecCNFSubset.subsetProgram` | `native_clause_relations::subset_program()`, 10×8 | The real framed literal iterator, preserving target, copying target for each query, running original encoded membership and clearing scratch; exits true only when no source literal is absent |
| `ExecClauseRelationsProgram.program` | `native_clause_relations::relation_program()`, 12×10 | Two directional source subset calls; outputs `reg10=equivalent(A,B)`, `reg11=strictSubset(A,B)`, `reg9=!subset(B,A)` while preserving both encoded clauses on stacks 8/9 |
| `ExecClauseRelationScan.program` | `native_clause_relation_scan::program(mode)`, 15×12 | Physical framed formula iteration in three source modes: equivalent, strict subset, and missing core; source ports tag 12, present 13, found 14, input 10, payload/output 11 |
| `ExecClauseRelationScan.Preserving.program` | `native_clause_dedup::preserving_scan_program(mode)`, 15×13 | Copy formula 12→10, scan actual relation, clear 10; preserves original full master formula 12 and query clause 9 |
| `ExecClauseFiltersProgram.callback(mode)` | `native_clause_dedup::filter_callback(mode)`, 15×16 | Physically transfer candidate to query 9, scan preserved formula, clear answer, restore framed payload, invert found to selected, invoke source frame writer |
| `ExecClauseDedupProgram.program` | `native_clause_dedup::program()`, 15×16 | Compare each clause against unread suffix, preserve **last equivalent occurrence**, restore original clause order |
| `ExecClauseFiltersProgram.selfFilterProgram .strictSubset` | `native_clause_filter::self_filter_program(Mode::StrictSubset)`, 15×16 | Preserve full master, filter clauses with another strictly included clause, clear master, reverse the retained records into original order |
| `SubexpNormalizationProgram.program` | `native_normalization_full::program()`, 15×16 | Exact `prefixCall; dedupCall; removeSupersetsCall` on input/output stack 13: literal cleanup → tautology removal → clause deduplication → strict-superset removal |
| `Native.normalizationCommand` | `native_outer_normalization::command()`, 80×1220 | Source identity register lift 0..14; stack port map `[0..12,1218,14,15]`, putting normalized body on 1218 while retaining original input 256 and binary ambient 267 |

The prefix source's 13×11-to-15×16 stack map is **`[13,12,11,10,9,8,7,6,5,4,3]`**, with register identities 0..12. All source `Fin.castAdd` maps are identities; the source's explicit `Fin.natAdd` maps are not. The final normalized-body machine uses only source Boolean one-bit register and stack operations. Formula encodings and empty work-port preconditions are those established by the original Lean frontend.

Pinned Lean blobs newly added:
- `ExecClauseRelationsProgram.lean`: a8862641948df4ee03cb862620e57e83f53377cb`
- `ExecClauseRelationScan.lean`: 93acc8df0a368fd9622da096398fc089744a1b86`
- `ExecClauseRelationScanPreserve.lean`: ec00efddffa997aa08d56b45d7fcade6ce5fac5a`
- `ExecClauseFiltersProgram.lean`: e342d0b71061aa1592a2779dfa0cb4a3cba92303`
- `ExecClauseDedupProgram.lean`: aa56072041911f2ba7a6995ec39026e0495cd248`
- `ExecClauseSelfFilterProgram.lean`: 06d1d8833679a3fd4342e217f72a5f9d46866e42`
- Already pinned `SubexpNormalizationProgram.lean`: 0d425a55a1d936dda93b1638fad908a51627cee6`

## Executed local verification

Using restored and version-pinned **Rust 1.99.1**, local offline source-native v0.16.0 crate with prior M2 dependencies restored:

- `cargo test --offline --locked`: **141 tests passed** in debug.
- `cargo test --offline --locked --release`: **141 tests passed** in release.
- `cargo fmt --check`: **passed**.
- `cargo clippy --offline --locked --all-targets -- -D warnings`: **passed**.
- Tests include original clause-pair comparisons (empty, repeated and overlapping literal records), all three encoded formula relation modes, preserving-source scans, last-occurrence equivalence deduplication, strict subset self-filtering, physical four-pass normalization on fixed and randomized CNFs, explicit maximum-step failure, and outer 80×1220 ABI frame preservation.
- The **six new production Rust files and two committed acceptance-test files** have **exact identical Git blob SHA** to their locally compiled/tested versions. Additional detailed local-only relation, clause-dedup and full-normalization tests passed, but are not included in this increment.

The new stage registry is **68 unique, topologically ordered, source-pinned and final-theorem-reachable stages**, 100 pinned source blobs, zero missing/forward dependencies and zero orphan stages, based on a live GitHub branch source audit.

## Explicit remaining verification boundary

This is a **complete executable normalization subprogram**, not a complete ETH solver or TM2 theorem. The local source snapshot does **not** contain all concurrent GitHub-only M1/M2 modules and `remaining.rs`; consequently, the **combined exact GitHub HEAD has not been independently compiled**, and original imported-Lean differential execution has not been performed. A source pin and source-defined instruction similarity are not machine-refinement or bit-complexity proofs.

The original `Native.frontendCommand` still requires composing the already ported native header, this normalized-body command, and the existing body-placement/ambient suffix. Its registry status **remains Stub**, pending exact-head integration tests of that whole 80×1220 path. High-query reconstruction, nonterminal native leaf, disjoint DFS, and TM2 primitive bounds are also outstanding. No fabricated CNF count or semantic host fallback is introduced.
