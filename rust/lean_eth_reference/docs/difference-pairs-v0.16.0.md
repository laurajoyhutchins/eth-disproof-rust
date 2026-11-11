# Source-defined pair DFS (v0.16.0)

Pinned to `openai/math@4eaee87548250b2682affda7d05d947c05554bae`:

- `SqrtLogSpace/DifferencePairsProgram.lean`: `Ports`, `enter`, `nextOutside`, `backtrack`, `descend`, `body`, `command`, `program`
- `SqrtLogSpace/DifferencePairs.lean`: independent `words n J`, `pairCount n J`
- `SqrtLogSpace/QueryStreamProgram.lean`: `pairPorts = [35..39]/[832..835]` and `pairs`
- `SqrtLogSpace/QueryExecution.lean`: `PairStart.command = clearWord 851; expandCaller`

## Exact executable boundary

`native_difference_pairs::PairPorts::command(callback)` constructs the literal static structured controller, without accumulating a list of pairs and without a Rust callback closure. The callback is an input **machine command** compiled into the fixed table. The source tests supply a physically executed copy/push callback and an integrated `PairStart` + `expandCaller` callback.

Given unary `n` on stack 832 and unary `J` on 833, the controller visits the strict family of pairs `U ⊆ E`, `|E| < J` in exactly the original recursive `DifferencePairs.words` order. At each callback, stacks 834 (E) and 835 (U) hold the *reversed* coordinate-order Boolean masks, matching the Lean `Cursor` invariant. The callback preserves those four controller stacks while it executes. After the traversal, the original unary depth/budget are restored, pair-mask stacks are empty, and guard register 36 is false.

`pair_start_command()` clears the source dictionary 851 and calls the already executable physical mask expansion. `query_pairs_with_pair_start(after)` composes the real prefix with a separately supplied suffix. The complete production callback `SignatureTupleComplete.command QueryAssembler.commitPair` is **not yet implemented**; neither the signed algebraic contribution nor `QueryNodeFinish.command` is executable here. Never mark the complete `QueryStreamProgram.pairCallback` or `QueryStreamProgram.program` finished on this basis.

## Tests and limits

Tests compare execution to a *separate recursive reference*, not another implementation of the same controller. They cover strict budgets including zero and >n, complete visit order, guards, working-stack restoration, callback register clobbering, 512 levels with `J=1`, bounded-instruction refusal, and setup + expansion on every mask up to six ambient coordinates. The independent oracle lists words **only in tests**. Production command construction uses a fixed-depth instruction table independent of `n`, `J`, or the number of emitted pairs.

The full runtime of the DFS can be exponential in `n`, and a successful local Rust trace does not establish imported-Lean differential execution or the paper's stronger complexity result. Machine limits refuse rather than asserting an unverified completion.
