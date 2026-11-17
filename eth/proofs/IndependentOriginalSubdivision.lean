import Mathlib
import IndependentOriginalActiveWires

/-!
# Incidence-preserving equality-wire subdivision

OpenAI's October 25 appendix describes subdividing each wire by an
equality tensor to obtain a bipartite tensor network.

For the *real active cross-cluster link wires* of Anthropic's original
SatNet.net, this module performs that exact local rewrite: replace
the one shared Boolean variable on each original link by a left and
a right port, with the indicator [left = right] between them.

The proof preserves the original endpoint-specific factors and node
weights, exactly and without multiplicity. The result establishes
this common graph-rewrite step, NOT equality of OpenAI's separately
specified clause/equality-tree CNF constructor with Anthropic's
actual SAT network.
-/

namespace IndependentETH.OriginalSubdivision

open scoped BigOperators
open Finset
open IndependentETH.SourceIncidence
open IndependentETH.OriginalSatNet
open IndependentETH.OriginalActiveWires

/-- Equality tensor on each original Boolean wire. -/
def copyTensor {W R : Type*} [Fintype W] [CommSemiring R]
    (left right : W → Bool) : R :=
  ∏ w : W, if left w = right w then 1 else 0

/-- The complete product of equality tensors is the Kronecker
delta on global port assignments, including zero wires. -/
theorem copyTensor_eq {W R : Type*} [Fintype W] [CommSemiring R]
    (left right : W → Bool) :
    copyTensor (R := R) left right =
      if left = right then 1 else 0 := by
  classical
  by_cases h : left = right
  · subst right
    simp [copyTensor]
  · have hw : ∃ w : W, left w ≠ right w := by
      by_contra hn
      apply h
      funext w
      by_contra hne
      exact hn ⟨w, hne⟩
    obtain ⟨w, hne⟩ := hw
    have hz :
        (∏ t : W, if left t = right t then (1 : R) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hne])
    simp [copyTensor, h, hz]

/-- Inserting a two-port equality tensor on every wire is an exact
contraction identity over any commutative semiring. -/
theorem split_shared_assignment {W R : Type*}
    [Fintype W] [CommSemiring R]
    (first second : (W → Bool) → R) :
    (∑ bits : W → Bool, first bits * second bits) =
      ∑ left : W → Bool, ∑ right : W → Bool,
        first left * second right *
          copyTensor left right := by
  classical
  symm
  calc
    _ = ∑ left : W → Bool, ∑ right : W → Bool,
          first left * second right *
            (if left = right then (1 : R) else 0) := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      rw [copyTensor_eq]
    _ = ∑ bits : W → Bool, first bits * second bits := by
      simp [mul_ite, mul_assoc]

variable (φ : List (List (ℕ × Bool))) (g μ k : ℕ)

abbrev Wire := IndependentETH.OriginalActiveWires.ActiveWire φ g μ k

/-- The unmodified first endpoint factor at all original pair
incidences, evaluated on the left copy of the real link bits. -/
def leftProduct
    (z : Fin g → Groundwork.SatNet.Sl μ k → Bool)
    (bits : Wire φ g μ k → Bool) : ℤ :=
  ∏ p : PairEdge (Fin g),
    firstFactor (original φ g μ k) z (decodeWires φ g μ k bits) p

/-- The unmodified second endpoint factor at all original pair
incidences, evaluated on the right copy of the same links. -/
def rightProduct
    (z : Fin g → Groundwork.SatNet.Sl μ k → Bool)
    (bits : Wire φ g μ k → Bool) : ℤ :=
  ∏ p : PairEdge (Fin g),
    secondFactor (original φ g μ k) z (decodeWires φ g μ k bits) p

/-- Source-derived bipartite form: each original link is split into
left and right edge bits, glued by an equality tensor. Node-state
weights and endpoint factors are exactly the original declarations. -/
def subdividedValue : ℤ :=
  let N := original φ g μ k
  ∑ z ∈ Fintype.piFinset N.S,
    ∑ left : Wire φ g μ k → Bool,
      ∑ right : Wire φ g μ k → Bool,
        (((∏ a, N.W a (z a)) * leftProduct φ g μ k z left) *
            rightProduct φ g μ k z right) *
          copyTensor left right

/-- The original source network has the same exact contraction as
the explicitly subdivided Boolean-wire graph. No sign, factor, or
edge multiplicity changes, even for empty graphs. -/
theorem original_value_eq_subdivided :
    (original φ g μ k).value = subdividedValue φ g μ k := by
  classical
  rw [original_value_eq_active_wires]
  unfold activeWireValue subdividedValue
  apply Finset.sum_congr rfl
  intro z _
  calc
    (∑ bits : Wire φ g μ k → Bool,
        (∏ a, (original φ g μ k).W a (z a)) *
          (∏ p : PairEdge (Fin g),
            firstFactor (original φ g μ k) z
              (decodeWires φ g μ k bits) p *
            secondFactor (original φ g μ k) z
              (decodeWires φ g μ k bits) p)) =
      ∑ bits : Wire φ g μ k → Bool,
        ((∏ a, (original φ g μ k).W a (z a)) *
          leftProduct φ g μ k z bits) *
          rightProduct φ g μ k z bits := by
      apply Finset.sum_congr rfl
      intro bits _
      simp [leftProduct, rightProduct, Finset.prod_mul_distrib, mul_assoc]
    _ = ∑ left : Wire φ g μ k → Bool,
        ∑ right : Wire φ g μ k → Bool,
          (((∏ a, (original φ g μ k).W a (z a)) *
            leftProduct φ g μ k z left) *
              rightProduct φ g μ k z right) *
              copyTensor left right :=
        split_shared_assignment
          (fun bits => (∏ a, (original φ g μ k).W a (z a)) *
            leftProduct φ g μ k z bits)
          (rightProduct φ g μ k z)

#print axioms IndependentETH.OriginalSubdivision.copyTensor_eq
#print axioms IndependentETH.OriginalSubdivision.split_shared_assignment
#print axioms IndependentETH.OriginalSubdivision.original_value_eq_subdivided

end IndependentETH.OriginalSubdivision
