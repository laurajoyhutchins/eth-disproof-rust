import Mathlib

/-!
# Packet factors and independent network factors: the normalization boundary

Pinned sources:
* OpenAI, math@4eaee87548250b2682affda7d05d947c05554bae,
  October 25 manuscript, appendix tensor-contraction, equations
  tensor-cauchy, tensor-mode-expansion and tensor-recursion-identity.
* Anthropic, formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
  eth/proof/networks/Paper/SecNetworks_DefFactor.lean and
  eth/proof/networks/Groundwork/Net/Net.lean.

The OpenAI packet child is formed by extracting a coefficient of a product
of row-affine factors and multiplying the source-mode powers. Anthropic
factors a pair interaction through a shared finite label. In general those
are different factorizations, and an equality of network values does not
identify the factor tables.

These results establish the canonical finite-label factorization, the
single-slot equality-gate correspondence at OpenAI's T = 0, the gauge
nonuniqueness of factor tables, and a weight-one integral obstruction.
They deliberately do NOT claim a full original-packet/Anthropic adapter
or any asymptotic running-time bound.
-/

namespace IndependentETH.PacketFactorBoundary

open scoped BigOperators

/--
Every finite integer interaction F(x,y) factors through the complete
column-state label set. This is an exact algebraic construction, but its
label set can be exponentially large. It is not Anthropic's quantitative
rank bound.
-/
theorem finite_relation_factors_through_columns
    {X Y : Type*} [Fintype Y]
    (F : X → Y → ℤ) (x : X) (y : Y) :
    F x y =
      ∑ label : Y, F x label * (if label = y then (1 : ℤ) else 0) := by
  classical
  simp only [mul_ite, mul_one, mul_zero]
  simp

/--
The affine row kernel l_y(x), used by OpenAI at W(0) = I.
For a single occupied slot its value is exactly the equality gate.
-/
def singleSlotRow (y x : Bool) : ℤ :=
  if y then (x.toNat : ℤ) else 1 - (x.toNat : ℤ)

/--
At T=0 a single-slot packet has W(0)=1. Its row factor agrees with
the edge interaction obtained by summing Anthropic-style delta factors
over one shared bit. The two delta factors are NOT each equal to the
original singleSlotRow function.
-/
theorem single_slot_interaction_equals_factored_edge
    (y x : Bool) :
    singleSlotRow y x =
      ∑ label : Bool,
        (if y = label then (1 : ℤ) else 0) *
        (if x = label then (1 : ℤ) else 0) := by
  cases y <;> cases x <;> decide

/--
An invertible diagonal sign change on the shared labels preserves a
pair interaction, even though it changes both of the individual factors.
Thus equality of complete interactions never uniquely determines the
constituent factor tables.
-/
theorem pair_factor_sign_gauge
    {Θ : Type*} [Fintype Θ]
    (f g ε : Θ → ℤ) (hε : ∀ θ, ε θ * ε θ = 1) :
    (∑ θ, f θ * g θ) =
      ∑ θ, (ε θ * f θ) * (ε θ * g θ) := by
  classical
  apply Finset.sum_congr rfl
  intro θ _
  calc
    f θ * g θ = (ε θ * ε θ) * (f θ * g θ) := by rw [hε θ, one_mul]
    _ = (ε θ * f θ) * (ε θ * g θ) := by ring

/-- Concrete distinct factor pairs with the same one-label interaction. -/
theorem same_interaction_distinct_factors :
    (1 : ℤ) * 1 = (-1 : ℤ) * (-1) ∧ (1 : ℤ) ≠ -1 := by
  norm_num

/--
Even after summing each group's local states, a group-dependent scalar
twist with product one preserves the product of group factors. Factor
equality is stronger than equality of the assembled contraction.
-/
theorem neutral_group_rescaling
    {G : Type*} [Fintype G]
    {X : G → Type*} [∀ g, Fintype (X g)]
    (entry : (g : G) → X g → ℤ)
    (scale : G → ℤ)
    (hscale : (∏ g, scale g) = 1) :
    (∏ g, ∑ x : X g, scale g * entry g x) =
      ∏ g, ∑ x : X g, entry g x := by
  classical
  calc
    (∏ g, ∑ x : X g, scale g * entry g x) =
        ∏ g, scale g * (∑ x : X g, entry g x) := by
          apply Finset.prod_congr rfl
          intro g _
          rw [Finset.mul_sum]
    _ = (∏ g, scale g) * (∏ g, ∑ x : X g, entry g x) := by
          rw [Finset.prod_mul_distrib]
    _ = _ := by rw [hscale, one_mul]

/--
OpenAI's weight-one packet-mode coefficients are divisible by 2, by the
specific geometric expansion in the manuscript. The signed integer
singlet correction in Anthropic's SWAP = I - vv^T has an entry -1,
which is not of that form.

This refutes the naive INTEGER, weight-preserving, coefficientwise
identification of those two specific kinds of modes. It does not refute
equality after a different change of basis or cancellation of modes.
-/
theorem odd_singlet_not_an_integral_weight_one_packet_coefficient :
    ¬ ∃ coefficient : ℤ, (2 : ℤ) * coefficient = -1 := by
  rintro ⟨coefficient, h⟩
  omega

#print axioms IndependentETH.PacketFactorBoundary.finite_relation_factors_through_columns
#print axioms IndependentETH.PacketFactorBoundary.single_slot_interaction_equals_factored_edge
#print axioms IndependentETH.PacketFactorBoundary.pair_factor_sign_gauge
#print axioms IndependentETH.PacketFactorBoundary.same_interaction_distinct_factors
#print axioms IndependentETH.PacketFactorBoundary.neutral_group_rescaling
#print axioms IndependentETH.PacketFactorBoundary.odd_singlet_not_an_integral_weight_one_packet_coefficient

end IndependentETH.PacketFactorBoundary
