import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointSparsify

/-! Direct evaluation of upstream source definitions. The CI job checks out
openai/math at the pinned revision. This file imports and calls that source;
it does not reimplement SAT.normalize or DisjointBranch.childA/childB. -/

namespace SourcePinnedTrace

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

private def pos (i : Fin 3) : SAT.Literal (Fin 3) := ⟨i, true⟩
private def neg (i : Fin 3) : SAT.Literal (Fin 3) := ⟨i, false⟩

private def make (rows : List (List (SAT.Literal (Fin 3)))) : SAT.CNF (Fin 3) :=
  (rows.map List.toFinset).toFinset

private def raw : SAT.CNF (Fin 3) := make [
  [pos 0, neg 0], [pos 0, pos 1], [pos 0]
]

private def shared : SAT.CNF (Fin 3) := make [
  [pos 0, pos 1], [pos 0, pos 2]
]

private def negativeShared : SAT.CNF (Fin 3) := make [
  [neg 0, pos 1], [neg 0, pos 2], [pos 1, pos 2]
]

private def bitString (w : List Bool) : String :=
  String.ofList (w.map fun bit => if bit then '1' else '0')

private def assignment (mask : Nat) : SAT.Assignment (Fin 3) :=
  fun i => (mask / (2 ^ i.val)) % 2 == 1

private def truthString (F : SAT.CNF (Fin 3)) : String :=
  bitString ((List.range 8).map fun mask => SAT.CNF.eval (assignment mask) F)

private def printCNF (name : String) {n : Nat} (F : SAT.CNF (Fin n)) : IO Unit :=
  IO.println (name ++ "|" ++ bitString (Encoding.encodeCNF F))

def main : IO Unit := do
  printCNF "empty0" (∅ : SAT.CNF (Fin 0))
  printCNF "empty3" (∅ : SAT.CNF (Fin 3))
  printCNF "normalized" (SAT.normalize raw)
  printCNF "shared" shared
  printCNF "branchA" (DisjointBranch.childA shared 2 ({pos 0} : SAT.Clause (Fin 3)))
  printCNF "branchB" (DisjointBranch.childB shared 2 ({pos 0} : SAT.Clause (Fin 3)))
  printCNF "negativeA" (DisjointBranch.childA negativeShared 2 ({neg 0} : SAT.Clause (Fin 3)))
  printCNF "negativeB" (DisjointBranch.childB negativeShared 2 ({neg 0} : SAT.Clause (Fin 3)))
  IO.println ("truthSource|" ++ truthString shared)
  IO.println ("truthA|" ++ truthString (DisjointBranch.childA shared 2 ({pos 0} : SAT.Clause (Fin 3))))
  IO.println ("truthB|" ++ truthString (DisjointBranch.childB shared 2 ({pos 0} : SAT.Clause (Fin 3))))

end SourcePinnedTrace

def main : IO Unit := SourcePinnedTrace.main
