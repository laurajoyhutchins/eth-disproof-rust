namespace MutFixture
inductive PairLike where
  | empty
  | one (value : Nat)
  | two (left right : Nat)

def rotate (x : PairLike) : PairLike :=
  match x with
  | .empty => .empty
  | .one a => .two a (a + 1)
  | .two a b => .two b a

def first (x : PairLike) : Nat :=
  match x with
  | .empty => 0
  | .one a => a
  | .two a _ => a

def unique (a b : Nat) : Nat :=
  first (rotate (.two a b))

def shared (a b : Nat) : Nat :=
  let original := PairLike.two a b
  first (rotate original) + first original
end MutFixture
