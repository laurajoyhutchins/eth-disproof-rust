import RuntimeHeapKernels

/-!
Source-only reset/reuse candidates, intentionally not hand-authored IR.
The pinned Lean 4.34.1 compiler decides whether any final IR contains del.
Keep this independent of the Rust test-host shell deletion probes.
-/
namespace RuntimeHeapDel

open RuntimeHeap

@[noinline] def rebuild (x : Box) (newStamp : Nat) : Box :=
  match x with
  | .missing => .missing
  | .mk child _ => .mk child newStamp

@[noinline] def rebuildOrDiscard (x : Box) (newStamp : Nat) (keep : Bool) : Box :=
  match x with
  | .missing => .missing
  | .mk child _ =>
    if keep then .mk child newStamp else .missing

@[noinline] def rebuildOrExtract (x : Box) (newStamp : Nat) (rebuild : Bool) : Pair :=
  match x with
  | .missing => .vacant
  | .mk child _ =>
    if rebuild then payload (.mk child newStamp) else child

@[noinline] def rebuildThenExtract (x : Box) (newStamp : Nat) (rebuild : Bool) : Pair :=
  let changed := if rebuild then rebuildOrDiscard x newStamp true else x
  payload changed

#guard rebuildOrExtract (.mk (.mk 5 6) 7) 8 false == .mk 5 6
#guard rebuildOrExtract (.mk (.mk 5 6) 7) 8 true == .mk 5 6
#guard rebuildOrDiscard (.mk (.mk 5 6) 7) 8 false == .missing

end RuntimeHeapDel
