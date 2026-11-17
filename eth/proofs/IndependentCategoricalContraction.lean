import Mathlib

/-!
# Finite weighted-network composition and change of coefficients

A concrete algebraic core for a category of finite weighted relations.
Objects are finite boundary-state types, morphisms are matrices `A → B → R`,
composition sums over an internal boundary, and the monoidal product is the
Kronecker product. The lemmas prove the composition, unit, interchange,
trace, and base-change laws used by a string-diagram interpretation.

This is not an adapter for OpenAI's source-specific two-adic packets, and
proving these laws alone does not prove the ETH runtime or resource theorem.
-/

namespace IndependentETH.Categorical

open scoped BigOperators

/-- An `R`-weighted map between finite boundary-state types. -/
abbrev Kernel (R : Type*) (A B : Type*) := A → B → R

/-- Contract matching intermediate boundary labels. -/
def compose {R A B C : Type*} [Semiring R] [Fintype B]
    (f : Kernel R A B) (g : Kernel R B C) : Kernel R A C :=
  fun a c => ∑ b : B, f a b * g b c

/-- The equality wire. -/
def ident (R A : Type*) [Semiring R] [DecidableEq A] : Kernel R A A :=
  fun a b => if a = b then 1 else 0

/-- Parallel juxtaposition of independent networks. -/
def tensor {R A B C D : Type*} [Mul R]
    (f : Kernel R A B) (g : Kernel R C D) :
    Kernel R (A × C) (B × D) :=
  fun a b => f a.1 b.1 * g a.2 b.2

/-- The weighted-relation composition is associative. -/
theorem compose_assoc {R A B C D : Type*} [Semiring R]
    [Fintype B] [Fintype C]
    (f : Kernel R A B) (g : Kernel R B C) (h : Kernel R C D) :
    compose (compose f g) h = compose f (compose g h) := by
  funext a d
  change (∑ c : C, (∑ b : B, f a b * g b c) * h c d) =
    ∑ b : B, f a b * (∑ c : C, g b c * h c d)
  calc
    _ = ∑ c : C, ∑ b : B, (f a b * g b c) * h c d := by
      simp_rw [Finset.sum_mul]
    _ = ∑ b : B, ∑ c : C, f a b * (g b c * h c d) := by
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    _ = _ := by
      simp_rw [Finset.mul_sum]

/-- An identity wire before a network changes nothing. -/
theorem ident_compose {R A B : Type*} [Semiring R]
    [Fintype A] [DecidableEq A] (f : Kernel R A B) :
    compose (ident R A) f = f := by
  funext a b
  simp [compose, ident]

/-- An identity wire after a network changes nothing. -/
theorem compose_ident {R A B : Type*} [Semiring R]
    [Fintype B] [DecidableEq B] (f : Kernel R A B) :
    compose f (ident R B) = f := by
  funext a b
  simp [compose, ident]

/-- Interchange law: two independent contractions can be performed separately. -/
theorem tensor_compose {R A B C D E F : Type*} [CommSemiring R]
    [Fintype B] [Fintype D]
    (f₁ : Kernel R A B) (f₂ : Kernel R B E)
    (g₁ : Kernel R C D) (g₂ : Kernel R D F) :
    compose (tensor f₁ g₁) (tensor f₂ g₂) =
      tensor (compose f₁ f₂) (compose g₁ g₂) := by
  funext ac ef
  change (∑ bd : B × D,
      (f₁ ac.1 bd.1 * g₁ ac.2 bd.2) *
        (f₂ bd.1 ef.1 * g₂ bd.2 ef.2)) =
    (∑ b : B, f₁ ac.1 b * f₂ b ef.1) *
      (∑ d : D, g₁ ac.2 d * g₂ d ef.2)
  calc
    _ = ∑ b : B, ∑ d : D,
        (f₁ ac.1 b * f₂ b ef.1) *
          (g₁ ac.2 d * g₂ d ef.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = ∑ b : B, (f₁ ac.1 b * f₂ b ef.1) *
        (∑ d : D, g₁ ac.2 d * g₂ d ef.2) := by
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_mul]

/-- Entrywise symmetry of the tensor product under exchange of both ports. -/
theorem tensor_swap {R A B C D : Type*} [CommSemiring R]
    (f : Kernel R A B) (g : Kernel R C D)
    (ac : A × C) (bd : B × D) :
    tensor f g ac bd = tensor g f (ac.2, ac.1) (bd.2, bd.1) := by
  simp [tensor, mul_comm]

/-- Close all output wires onto corresponding input wires. -/
def trace {R A : Type*} [AddCommMonoid R] [Fintype A]
    (f : Kernel R A A) : R := ∑ a : A, f a a

/-- Cyclicity of a finite tensor-network contraction. -/
theorem trace_compose {R A B : Type*} [CommSemiring R]
    [Fintype A] [Fintype B]
    (f : Kernel R A B) (g : Kernel R B A) :
    trace (compose f g) = trace (compose g f) := by
  change (∑ a : A, ∑ b : B, f a b * g b a) =
    ∑ b : B, ∑ a : A, g b a * f a b
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

/-- Closing a juxtaposed pair equals the product of individual closures. -/
theorem trace_tensor {R A B : Type*} [CommSemiring R]
    [Fintype A] [Fintype B]
    (f : Kernel R A A) (g : Kernel R B B) :
    trace (tensor f g) = trace f * trace g := by
  change (∑ ab : A × B, f ab.1 ab.1 * g ab.2 ab.2) =
    (∑ a : A, f a a) * (∑ b : B, g b b)
  calc
    _ = ∑ a : A, ∑ b : B, f a a * g b b := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : A, f a a * (∑ b : B, g b b) := by
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_mul]

/-- The closure operation is additive. -/
theorem trace_add {R A : Type*} [AddCommMonoid R] [Fintype A]
    (f g : Kernel R A A) :
    trace (fun a b => f a b + g a b) = trace f + trace g := by
  simp [trace, Finset.sum_add_distrib]

/-- Applying a semiring homomorphism entrywise to a weighted relation. -/
def mapKernel {R S A B : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (f : Kernel R A B) : Kernel S A B :=
  fun a b => φ (f a b)

/-- Coefficient change respects contraction (the functorial square). -/
theorem map_compose {R S A B C : Type*} [Semiring R] [Semiring S]
    [Fintype B] (φ : R →+* S)
    (f : Kernel R A B) (g : Kernel R B C) :
    mapKernel φ (compose f g) =
      compose (mapKernel φ f) (mapKernel φ g) := by
  funext a c
  simp [mapKernel, compose]

/-- Coefficient change respects identity wires. -/
theorem map_ident {R S A : Type*} [Semiring R] [Semiring S]
    [DecidableEq A] (φ : R →+* S) :
    mapKernel φ (ident R A) = ident S A := by
  funext a b
  simp [mapKernel, ident]

/-- Coefficient change respects parallel juxtaposition (monoidality). -/
theorem map_tensor {R S A B C D : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (f : Kernel R A B) (g : Kernel R C D) :
    mapKernel φ (tensor f g) =
      tensor (mapKernel φ f) (mapKernel φ g) := by
  funext ac bd
  simp [mapKernel, tensor]

/-- Coefficient change commutes with closing all wires (naturality). -/
theorem map_trace {R S A : Type*} [Semiring R] [Semiring S]
    [Fintype A] (φ : R →+* S) (f : Kernel R A A) :
    φ (trace f) = trace (mapKernel φ f) := by
  simp [mapKernel, trace]

/-- Every fixed finite signed sum of scalar evaluations commutes with base change. -/
theorem map_weighted_sum {R S I : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (modes : Finset I)
    (coeff value : I → R) :
    φ (∑ i ∈ modes, coeff i * value i) =
      ∑ i ∈ modes, φ (coeff i) * φ (value i) := by
  simp

#print axioms IndependentETH.Categorical.compose_assoc
#print axioms IndependentETH.Categorical.ident_compose
#print axioms IndependentETH.Categorical.compose_ident
#print axioms IndependentETH.Categorical.tensor_compose
#print axioms IndependentETH.Categorical.tensor_swap
#print axioms IndependentETH.Categorical.trace_compose
#print axioms IndependentETH.Categorical.trace_tensor
#print axioms IndependentETH.Categorical.trace_add
#print axioms IndependentETH.Categorical.map_compose
#print axioms IndependentETH.Categorical.map_ident
#print axioms IndependentETH.Categorical.map_tensor
#print axioms IndependentETH.Categorical.map_trace
#print axioms IndependentETH.Categorical.map_weighted_sum

end IndependentETH.Categorical
