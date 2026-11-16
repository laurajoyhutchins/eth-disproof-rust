import NativeRust

namespace LCNFProbe

@[noinline] def bump (x : UInt64) : UInt64 := x + 1

def select (x y : UInt64) : UInt64 :=
  let chosen := if x < y then bump x else bump y
  chosen + 5

def tailOrEmpty (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | _ :: tail => tail

end LCNFProbe

#native_rust_closure LCNFProbe.select as "select" to "artifacts/lcnf-baseline.rs"
