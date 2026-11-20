# Source-native framed record scanners

Source pin: [OpenAI `openai/math@4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae).

This is a comparison of **finite source-machine programs**. The shared
framing and traversal do not imply interchangeable predicates, identical
stack effects, or a complete verified SAT algorithm.

## Structure shared by the six callers

Each scanner invokes the exact seven-label `ParserProgram.frameProgram`
via `Cmd::Call(frame_program()?.lift(...))`, and composes it through the
existing `RecordPrograms.iterate` structured command:

```text
found := false
(tag, present) := pop(source)
while tag:
    parse one framed payload into payload stack
    caller's callback
    if found: tag := false
    else: (tag, present) := pop(source)
```

In this encoding `source` is the unread list, `payload` is a **physical
stack containing reversed frame bits**, `tag` is the current list tag,
`present` reports the last pop and `found` can stop iteration early
without consuming the next record. Every operation remains a physical
`Cmd` node. The abstract shape is not a host iteration.

`bit_program/record_iteration.rs` now owns the two-register/two-stack
frame-reader lift as well as the existing iterator. `iterate_framed`
takes the physical port map and a caller-supplied callback; it refuses
an out-of-range or noninjective frame-reader mapping through the
original `Program::lift` validation. It does **not** validate that the
input bit stream obeys the caller's canonical framing precondition.

## Physical interfaces, not interchangeable policies

| Caller | Machine | `tag / present / found` | `source -> payload` | Callback and downstream contract |
| --- | --- | --- | --- | --- |
| Clause dedup scan | 15 regs, 16 stacks | 0 / 1 / 14 | 13 -> 15 | Preserving equivalence comparison against unread suffix; emit survivors, then reverse in full dedup |
| Clause self-filter scan | 15 regs, 16 stacks | 0 / 1 / 14 | 13 -> 15 | Fixed-master predicate for Equivalent, StrictSubset or MissingCore; full command copies master then reverses output |
| Clause relation scan | 15 regs, 12 stacks | 12 / 13 / 14 | 10 -> 11 | Transfer candidate, run relation machine, copy one of registers 10 / 11 / 9 to `found`, clear comparison scratch; outer command pushes result |
| Tautology scan | 13 regs, 11 stacks | 10 / 11 / 12 | 0 -> 1 | Tautology-core predicate, negate selection, emit/discard, reverse in full filter |
| Encoded membership scan | 7 regs, 5 stacks | 5 / 6 / 4 | 0 -> 1 | Preserve query on 2, equality-check payload against its copy, clear comparison stacks; outer command pushes found |
| Record reversal | 3 regs, 4 stacks | 0 / 1 / 2 | 0 -> 3 | Force selection, physically emit record, then reset `found`; iteration is *not* an early-match search |

The **row-specific values are part of the source ABI**. Especially:
- Different register and stack maps cannot be merged by using a single
  magic default. Valid frame reader maps must be injective and in range.
- A callback that leaves `found=true` stops at the current record; the
  reversal callback deliberately resets it so traversal continues.
- Relation modes choose different source result registers. The
  deduplication callback first copies the *unread suffix* for its
  comparison; self-filtering uses a fixed master. These are not
  equivalent callbacks even though both use the 15x16 framing map.
- Terminal output pushes, order restoration, scratch clearing and
  input preconditions are **outside** this iterator and remain in their
  respective modules. Never infer them from a shared loop.

## Regression obligations

`eth/tests/source_record_iteration.rs` independently reconstructs the
**pre-extraction** command tree, including each lifted frame parser,
all callbacks and each of the three relation/filter modes. It compares
the entire `Cmd` tree and its compiled `Program` (ports, entry,
all physical instructions and labels). A separate negative test proves
that different scanner policies remain different command trees.

The iterator's unit tests check invalid physical reader maps,
a synthetic early-found callback leaving the next framed record
unread and a false callback scanning to the final terminator.
These are bounded executable tests. They do not establish
Lean-to-Rust compiler refinement, source-level complexity, or
a complete QueryStream execution.

Related: [Rust style](RUST_STYLE.md) and the technical notebook's
[Canonical StackRoutines study](https://github.com/laurajoyhutchins/technical-notebook/blob/main/content/studies/canonical-stack-routines.md).
