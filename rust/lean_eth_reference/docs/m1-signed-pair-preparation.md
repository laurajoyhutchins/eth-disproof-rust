# Milestone 1: signed-pair accumulator preparation

Source: `openai/math@4eaee87548250b2682affda7d05d947c05554bae`.

The original production query's callback is `PairStart → SignatureTupleComplete → QueryAssembler.commitPair`. The present increment implements **only** the exact finite `QueryAssembler.preparePair` command, leaving `pairUpdate` and the production signed commit unavailable. It must not be used to produce a numeric result by itself.

## Source command

1. `clearPair`: pay to clear the ordered 88-port `pairScratch` set: 0..55, 100..127, 159, 841, 848, 849. It is one compiled 16×896 `SubexpSetupStorage.clearMany` call lifted to 40×896.
2. `FactorEnvironment.bootstrap`: preserve/copy 194→5, 202→12, 203→17, 201→22, 204→39, 212→45, 243→46, with the physical temporary at 159.
3. `QueryTupleVisitor.overwrite 211 34`: physically clear destination 34 and preserve-copy 211→34 with temporary 841.

The Lean `Fin.castAdd 24` register embedding retains indices 0..15; it does not shift them to 24..39. Therefore the two scratch registers are 0 and 1. The commands preserve pair words 834/835, dictionary 851, accumulator 850, and retained source masters.

Source identity is pinned in `reference/source-manifest.json` for QueryAssembler, SubexpSetupStorage, FactorEnvironment and QueryTupleVisitor.

## Verified scope and resource evidence

`tests/native_pair_accumulator.rs` executes actual 40×896 instructions. It independently checks scratch membership and exclusivity, whole-stack preservation after clear, complete cache and scale-word recovery, dirty-scratch reentrancy across changed masters, stage composition and explicit resource refusal. The cost oracle is the **original instruction-count recurrence**:

```
clear = sum_{p in pairScratch} (2 * len(p) + 3) + 1
bootstrap = sum_{(src,dst) in cachePairs} (7 * len(src) + 5) + 1
overwrite = 7 * len(211) + 8     # port 34 is cleared beforehand
compiled_program = clear + bootstrap + overwrite + 1
```


**Still outstanding:** `QueryAssembler.pairUpdate`, `clearPair` after the update, production `SignatureTupleComplete.command`, `QueryStreamProgram.pairs` with real signed callback, and full query reconstruction. Do not mark those executable just because `preparePair` is.
