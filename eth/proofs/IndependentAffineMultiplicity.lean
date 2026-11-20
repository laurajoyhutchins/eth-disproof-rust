import Mathlib

/-!
# Inherited affine fiber multiplicities

A child affine interface has value 2^free times the indicator of its
residual boundary constraints. Merging two independently quantified
child interiors with a new local elimination multiplies the two inherited
powers of two and the new local power of two.

These are universal semiring identities and a finite-fold theorem.
They prove no Rust instruction, raw decoder, or source parser correct.
-/

namespace IndependentETH.AffineMultiplicity

/-- The exponent used by a two-child affine merge. -/
def mergedExponent (left right newFree : Nat) : Nat :=
  newFree + left + right

/-- The exact, cancellation-free multiplicity equation holds in any
commutative semiring, not merely when the coefficient is a Boolean. -/
theorem merged_factor {R : Type*} [CommSemiring R]
    (left right newFree : Nat) (f g : R) :
    ((2 : R) ^ left * f) * ((2 : R) ^ right * g) *
        ((2 : R) ^ newFree) =
      (2 : R) ^ (mergedExponent left right newFree) * (f * g) := by
  simp [mergedExponent, pow_add, mul_assoc, mul_left_comm, mul_comm]

/-- A complete left fold of the extra free dimensions contributed by
subsequent leaves and by local merge eliminations. -/
def carryFree : Nat → List (Nat × Nat) → Nat
  | total, [] => total
  | total, (nextLeaf, newFree) :: rest =>
      carryFree (total + nextLeaf + newFree) rest

theorem carryFree_eq (initial : Nat) (steps : List (Nat × Nat)) :
    carryFree initial steps =
      initial + (steps.map (fun pair => pair.1 + pair.2)).sum := by
  induction steps generalizing initial with
  | nil =>
      simp [carryFree]
  | cons pair rest ih =>
      rcases pair with ⟨nextLeaf, newFree⟩
      simp only [carryFree, List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- The final multiplicity factor decomposes into the first leaf and
every later leaf/local merge contribution, without enumerating any
hidden Boolean assignments. -/
theorem carryFree_power {R : Type*} [CommSemiring R]
    (initial : Nat) (steps : List (Nat × Nat)) :
    (2 : R) ^ (carryFree initial steps) =
      (2 : R) ^ initial *
        (2 : R) ^ ((steps.map (fun pair => pair.1 + pair.2)).sum) := by
  rw [carryFree_eq, pow_add]

#print axioms IndependentETH.AffineMultiplicity.merged_factor
#print axioms IndependentETH.AffineMultiplicity.carryFree_eq
#print axioms IndependentETH.AffineMultiplicity.carryFree_power

end IndependentETH.AffineMultiplicity
