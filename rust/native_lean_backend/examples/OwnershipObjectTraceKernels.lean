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

-- A two-level, heap-backed tree. Releasing its root must cascade through
-- an intermediate fork into the retained leaf, as well as into the root's
-- other direct child. Its source implementation is unchanged on both paths.
inductive Tree where
  | vacant
  | leaf (payload stamp : Nat)
  | fork (left right : Tree)

@[noinline] def createNested (a b : Nat) : Tree :=
  .fork (.fork (.leaf a (a + 1)) (.leaf b (b + 1)))
        (.leaf (a + b) (a + b + 1))

end OwnershipObjectTrace
