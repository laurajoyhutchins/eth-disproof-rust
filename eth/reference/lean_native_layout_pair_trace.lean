import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

/-!
Direct Lean-source physical trace for `NativeLayoutLoad.command` and
`PairNativeSetup.setupCaller` at
openai/math@4eaee87548250b2682affda7d05d947c05554bae.

Requires complete Lean 4.34.1 / pinned Mathlib; NOT EXECUTED in this session.
These are two independently executable source stages. The intervening native
head-loader is not ported, so this is NOT one complete query evaluation.
-/
namespace NativeLayoutPairTrace
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private def bitString (xs : List Bool) : String :=
  String.ofList (xs.map fun b => if b then '1' else '0')

private def run {r s l : Nat} (p : BitProgram.Program r s l) :
    Nat → BitProgram.Cfg r s l → Nat × BitProgram.Cfg r s l
  | 0, c => (0, c)
  | fuel + 1, c =>
    match BitProgram.step p c with
    | none => (0, c)
    | some next =>
      let (steps, out) := run p fuel next
      (steps + 1, out)

private def layoutStacks (seed : Nat) : Fin 896 → List Bool := fun i =>
  if 730 ≤ i.val ∧ i.val < 744 then
    List.replicate ((i.val - 730 + seed) % 4) (decide ((i.val + seed) % 2 = 0))
  else if 128 ≤ i.val ∧ i.val < 142 then [true, false]
  else if i = (684 : Fin 896) then [true, false, true]
  else if i = (660 : Fin 896) then [false, true]
  else if i = (665 : Fin 896) then [true]
  else if i = (789 : Fin 896) then [false, true]
  else []

private def pairMask (seed : Nat) : List Bool :=
  (List.range (seed + 2)).map fun j => decide ((j + seed) % 3 = 0)

private def pairStacks (seed : Nat) : Fin 896 → List Bool := fun i =>
  if i = (338 : Fin 896) then pairMask seed
  else if i = (243 : Fin 896) then [true, false, decide (seed % 2 = 0)]
  else if 325 ≤ i.val ∧ i.val < 330 then [true, false]
  else if i = (832 : Fin 896) then [false, true]
  else if i = (833 : Fin 896) then [false]
  else if i = (834 : Fin 896) then [true]
  else if i = (835 : Fin 896) then [true, false]
  else if i = (789 : Fin 896) then [true]
  else []

private def regs (seed : Nat) : Fin 40 → Bool :=
  fun i => decide ((i.val + seed) % 3 = 0)

private def masterWords {l : Nat} (c : BitProgram.Cfg 40 896 l) (base : Nat) : String :=
  String.intercalate "," ((List.range 14).map fun j => bitString (c.stacks (⟨(base + j) % 896, Nat.mod_lt _ (by decide)⟩)))

private def layoutLine {l : Nat} (seed steps : Nat) (c : BitProgram.Cfg 40 896 l) : String :=
  "layout|" ++ toString seed ++ "|" ++ toString steps ++ "|" ++
    masterWords c 128 ++ "|" ++ masterWords c 730 ++ "|" ++
    bitString (c.stacks 684) ++ "|" ++ bitString (c.stacks 660) ++ "|" ++
    bitString (c.stacks 665) ++ "|" ++
    (if c.regs 16 then "1" else "0") ++ "|" ++ (if c.regs 39 then "1" else "0")

private def pairLine {l : Nat} (seed steps : Nat) (c : BitProgram.Cfg 40 896 l) : String :=
  "pair|" ++ toString seed ++ "|" ++ toString steps ++ "|" ++
    bitString (c.stacks 338) ++ "|" ++ bitString (c.stacks 243) ++ "|" ++
    bitString (c.stacks 832) ++ "|" ++ bitString (c.stacks 833) ++ "|" ++
    String.intercalate "," ((List.range 5).map fun j => bitString (c.stacks (⟨(325+j) % 896, Nat.mod_lt _ (by decide)⟩))) ++ "|" ++
    bitString (c.stacks 834) ++ "|" ++ bitString (c.stacks 835) ++ "|" ++
    (if c.regs 9 then "1" else "0") ++ "|" ++ (if c.regs 39 then "1" else "0")

def main : IO Unit := do
  let lp := NativeLayoutLoad.program
  let cmd := PairNativeSetup.setupCaller
  let pp := StructuredCalls.compiled cmd 338 832
  for seed in [0,1,2,3] do
    let lc : BitProgram.Cfg 40 896 (StructuredCalls.size NativeLayoutLoad.command + 1) :=
      ⟨some lp.entry, regs seed, layoutStacks seed⟩
    let (ls, lf) := run lp 50000 lc
    unless lf.pc.isNone do
      throw (IO.userError s!"NativeLayoutLoad did not halt: {seed}")
    IO.println (layoutLine seed ls lf)
    let pc : BitProgram.Cfg 40 896 (StructuredCalls.size cmd + 1) :=
      ⟨some pp.entry, regs seed, pairStacks seed⟩
    let (ps, pf) := run pp 50000 pc
    unless pf.pc.isNone do
      throw (IO.userError s!"PairNativeSetup did not halt: {seed}")
    IO.println (pairLine seed ps pf)
end NativeLayoutPairTrace

def main : IO Unit := NativeLayoutPairTrace.main
