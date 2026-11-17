import Mathlib

/-!
# A small exact arithmetic circuit IR

This is the semantic starting point for Adaptive Certified Contraction (ACC).
It deliberately has no opaque "solve SAT" gate: source adapters must expose
their input factors as atoms, and arithmetic as scalar/add/mul.

The syntax is a tree. Hash-consing / explicit shared DAG nodes, constructive
optimization, and bit-cost bounds are separate obligations. Finite sums and
products are syntactic folds and are not claimed to be efficient.
-/

namespace ACC

universe u

inductive Circuit (Atom : Type u) : Type u where
  | scalar : ℤ → Circuit Atom
  | atom : Atom → Circuit Atom
  | add : Circuit Atom → Circuit Atom → Circuit Atom
  | mul : Circuit Atom → Circuit Atom → Circuit Atom

namespace Circuit

variable {Atom : Type u}

/-- Interpret only atomic source factors; all arithmetic is explicit. -/
def eval (env : Atom → ℤ) : Circuit Atom → ℤ
  | .scalar n => n
  | .atom a => env a
  | .add a b => eval env a + eval env b
  | .mul a b => eval env a * eval env b

/-- A finite syntactic sum; no implicit algebraic oracle. -/
def sumList (xs : List (Circuit Atom)) : Circuit Atom :=
  xs.foldr add (.scalar 0)

/-- A finite syntactic product. -/
def prodList (xs : List (Circuit Atom)) : Circuit Atom :=
  xs.foldr mul (.scalar 1)

@[simp] theorem eval_sumList (env : Atom → ℤ) (xs : List (Circuit Atom)) :
    eval env (sumList xs) = (xs.map (eval env)).sum := by
  induction xs with
  | nil => simp [sumList, eval]
  | cons x xs ih => simp [sumList, eval, ih]

@[simp] theorem eval_prodList (env : Atom → ℤ) (xs : List (Circuit Atom)) :
    eval env (prodList xs) = (xs.map (eval env)).prod := by
  induction xs with
  | nil => simp [prodList, eval]
  | cons x xs ih => simp [prodList, eval, ih]

/-- Finset-shaped gates are explicitly lowered to finite lists. -/
def sumFinset {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Circuit Atom) : Circuit Atom :=
  sumList (s.toList.map f)

def prodFinset {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Circuit Atom) : Circuit Atom :=
  prodList (s.toList.map f)

@[simp] theorem eval_sumFinset {α : Type*} [DecidableEq α]
    (env : Atom → ℤ) (s : Finset α) (f : α → Circuit Atom) :
    eval env (sumFinset s f) = ∑ a ∈ s, eval env (f a) := by
  classical
  simp [sumFinset, List.map_map]

@[simp] theorem eval_prodFinset {α : Type*} [DecidableEq α]
    (env : Atom → ℤ) (s : Finset α) (f : α → Circuit Atom) :
    eval env (prodFinset s f) = ∏ a ∈ s, eval env (f a) := by
  classical
  simp [prodFinset, List.map_map]

/-- A source-independent distributive circuit rewrite. -/
theorem eval_distribute (env : Atom → ℤ) (a b c : Circuit Atom) :
    eval env (.mul a (.add b c)) =
      eval env (.add (.mul a b) (.mul a c)) := by
  simp [eval, mul_add]

end Circuit

/-- A proof-carrying rewrite; sound under every interpretation of atoms. -/
structure CertifiedRewrite (Atom : Type u) where
  before : Circuit Atom
  after : Circuit Atom
  sound : ∀ env : Atom → ℤ,
    before.eval env = after.eval env

def CertifiedRewrite.distribute {Atom : Type u}
    (a b c : Circuit Atom) : CertifiedRewrite Atom where
  before := .mul a (.add b c)
  after := .add (.mul a b) (.mul a c)
  sound := fun env => Circuit.eval_distribute env a b c

/-- A pair of typed boundary interfaces with a retraction. -/
structure Boundary (V W : Type*) where
  encode : W → V
  decode : V → W
  retract : ∀ w, decode (encode w) = w

/-- Mathematically lower a map through two boundary interfaces. -/
def lower {V W X Y : Type*}
    (a : Boundary V W) (b : Boundary X Y)
    (f : V → X) : W → Y :=
  fun w => b.decode (f (a.encode w))

/--
The crucial closure condition: the original result must remain representable.
Without closure, local compression does not commute with composition.
-/
theorem lower_comp {V W X Y Z U : Type*}
    (a : Boundary V W) (b : Boundary X Y) (c : Boundary Z U)
    (f : X → Z) (g : V → X)
    (hclosed : ∀ w,
      b.encode (b.decode (g (a.encode w))) = g (a.encode w)) :
    lower a c (f ∘ g) = (lower b c f) ∘ (lower a b g) := by
  funext w
  simp only [lower, Function.comp_apply, hclosed]

theorem lower_sound {V W X Y : Type*}
    (a : Boundary V W) (b : Boundary X Y)
    (f : V → X) (g : W → Y)
    (hsim : ∀ w, f (a.encode w) = b.encode (g w)) :
    lower a b f = g := by
  funext w
  simp [lower, hsim, b.retract]

-- An explicit counterexample: the first map stores information in a
-- discarded coordinate, and the second map reads it back.
private def exampleBoundary : Boundary (ℤ × ℤ) ℤ where
  encode x := (x, 0)
  decode x := x.1
  retract _ := rfl

private def store (x : ℤ × ℤ) : ℤ × ℤ := (0, x.1)
private def recover (x : ℤ × ℤ) : ℤ × ℤ := (x.2, 0)

theorem closure_is_necessary :
    lower exampleBoundary exampleBoundary (recover ∘ store) ≠
      (lower exampleBoundary exampleBoundary recover) ∘
      (lower exampleBoundary exampleBoundary store) := by
  intro h
  have h1 := congrArg (fun f : ℤ → ℤ => f 1) h
  norm_num [lower, exampleBoundary, recover, store] at h1

#print axioms ACC.Circuit.eval_distribute
#print axioms ACC.lower_comp
#print axioms ACC.lower_sound
#print axioms ACC.closure_is_necessary

end ACC
