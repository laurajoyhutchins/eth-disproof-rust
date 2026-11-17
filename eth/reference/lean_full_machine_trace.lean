import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramBranches

/-!
Every source instruction of the UNMODIFIED pinned OpenAI Lean program.
The 2-register, 2-stack state is recorded at each PC, including the halt.
No native Rust model, recreated instruction table, or precomputed answers
are used to generate the Lean side of this differential test.
-/
namespace FullMachineTrace
open OAI.Algorithms.SubexponentialSAT

private def bit (b : Bool) : Char := if b then '1' else '0'
private def word (w : List Bool) : String := String.ofList (w.map bit)
private def pcString {l : Nat} (pc : Option (Fin l)) : String :=
  match pc with
  | none => "H"
  | some p => toString p.val

private def stateLine {l : Nat} (name : String) (step : Nat)
    (c : BitProgram.Cfg 2 2 l) : String :=
  "machine|" ++ name ++ "|" ++ toString step ++ "|" ++ pcString c.pc ++ "|" ++
  String.ofList ([bit (c.regs 0), bit (c.regs 1)]) ++ "|" ++
  word (c.stacks 0) ++ "|" ++ word (c.stacks 1)

private def run {l : Nat} (p : BitProgram.Program 2 2 l) (name : String) :
    Nat → Nat → BitProgram.Cfg 2 2 l → IO Unit
  | 0, _, _ => throw (IO.userError s!"source fuel exhausted on {name}")
  | fuel + 1, step, c => do
      IO.println (stateLine name step c)
      match BitProgram.step p c with
      | none => pure ()
      | some next => run p name fuel (step + 1) next

private def mask (size code : Nat) : List Bool :=
  (List.range size).map (fun i => code.testBit i)

def main : IO Unit := do
  let program := SqrtLog.HighIncidenceProgram.Branches.program
  for size in [0, 1, 2, 3, 4] do
    for code in List.range (2 ^ size) do
      for dirty in [false, true] do
        let name := toString size ++ "_" ++ toString code ++
          (if dirty then "_dirty" else "_clean")
        let init := BitProgram.initial program (mask size code)
        let start := if dirty then
          { init with regs := fun _ => true,
            «stacks» := Function.update init.stacks (1 : Fin 2) [true, false] }
          else init
        run program name 512 0 start

end FullMachineTrace

def main : IO Unit := FullMachineTrace.main
