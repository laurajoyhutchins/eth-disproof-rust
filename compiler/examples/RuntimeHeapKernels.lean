-- Unmodified source is independently compiled by Lean's C backend and
-- the existing pinned IR-to-Rust Reader. The fixture uses small Nat
-- fields; heap child ownership and arbitrary bignums remain unsupported.
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

#guard first (make 17 901) == 17
#guard observe 0 42 == 0

end RuntimeHeap
