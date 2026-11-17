-- Unmodified source is independently compiled by Lean's C backend and
-- the existing pinned IR-to-Rust Reader. The fixture uses small Nat
-- fields in Pair; the nested Box fixture exercises heap child ownership.
namespace RuntimeHeap

inductive Pair where
  | vacant
  | mk (left right : Nat)

@[noinline] def make (a b : Nat) : Pair := .mk a b

@[noinline] def first (p : Pair) : Nat :=
  match p with
  | .vacant => 0
  | .mk left _ => left

@[noinline] def observe (a b : Nat) : Nat := first (make a b)

inductive Box where
  | missing
  | mk (child : Pair) (stamp : Nat)

@[noinline] def nest (a b stamp : Nat) : Box :=
  .mk (make a b) stamp

@[noinline] def payload (x : Box) : Pair :=
  match x with
  | .missing => .vacant
  | .mk child _ => child

@[noinline] def nestedFirst (a b stamp : Nat) : Nat :=
  first (payload (nest a b stamp))

#guard nestedFirst 17 901 7 == 17
#guard first (make 17 901) == 17
#guard observe 0 42 == 0

end RuntimeHeap
