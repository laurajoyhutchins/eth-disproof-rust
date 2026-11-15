namespace OwnershipObjectTrace

-- Two constructors and two fields prevent the Lean compiler from
-- erasing this type to its single payload field.
inductive Token where
  | vacant
  | mk (payload stamp : Nat)

-- Every operation below is compiled unchanged to Lean C and native Rust.
-- Keep the explicit noinline boundary: the trace must cover actual calls.
@[noinline] def create (n : Nat) : Token := .mk n (n + 1)
@[noinline] def identity (x : Token) : Token := x
@[noinline] def select (chooseLeft : Bool) (x y : Token) : Token :=
  if chooseLeft then identity x else identity y

@[noinline] def applyValue (f : Nat → Token) (n : Nat) : Token := f n
@[noinline] def retain (x : Token) (_ : Nat) : Token := identity x
@[noinline] def throughClosure (x : Token) : Token :=
  applyValue (retain x) 0

end OwnershipObjectTrace
