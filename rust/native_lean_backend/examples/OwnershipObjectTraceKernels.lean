namespace OwnershipObjectTrace

inductive Token where
  | mk (payload : Nat)

-- Every operation below is compiled unchanged to Lean C and native Rust.
-- Keep the explicit noinline boundary: the trace must cover actual calls.
@[noinline] def create (n : Nat) : Token := .mk n
@[noinline] def identity (x : Token) : Token := x
@[noinline] def select (chooseLeft : Bool) (x y : Token) : Token :=
  if chooseLeft then identity x else identity y

@[noinline] def applyValue (f : Nat → Token) (n : Nat) : Token := f n
@[noinline] def retain (x : Token) (_ : Nat) : Token := identity x
@[noinline] def throughClosure (x : Token) : Token :=
  applyValue (retain x) 0

end OwnershipObjectTrace
