import Mathlib

/-!
# General GF(2) boundary fiber counting

For every finite linear map A and target t, the internal assignments
with A u = t are either empty or a translate of ker(A).
Thus every nonempty fiber has cardinality 2^(k-rank A).

This mathematical result does not itself certify the Rust row-operation
implementation, complexity, or the original OpenAI/Anthropic programs.
-/

namespace IndependentETH.AffineRankNullity

open Module

abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- Every nonempty affine fiber is in bijection with the homogeneous kernel. -/
noncomputable def fiberEquivKer
    {k m : ℕ}
    (A : Bits k →ₗ[ZMod 2] Bits m)
    (t : Bits m) (origin : Bits k) (h : A origin = t) :
    {u : Bits k // A u = t} ≃ LinearMap.ker A where
  toFun := fun u => ⟨u.val - origin, by
    change A (u.val - origin) = 0
    rw [map_sub, u.property, h, sub_self]⟩
  invFun := fun v => ⟨v.val + origin, by
    change A (v.val + origin) = t
    rw [map_add, v.property, h, zero_add]⟩
  left_inv := by
    intro u
    apply Subtype.ext
    simp
  right_inv := by
    intro v
    apply Subtype.ext
    simp

/-- Rank-nullity and finite-field cardinality give the kernel size. -/
theorem card_kernel_eq_pow
    {k m : ℕ} (A : Bits k →ₗ[ZMod 2] Bits m) :
    Fintype.card (LinearMap.ker A) =
      2 ^ (k - Module.finrank (ZMod 2) (LinearMap.range A)) := by
  classical
  have h : Module.finrank (ZMod 2) (LinearMap.ker A) =
      k - Module.finrank (ZMod 2) (LinearMap.range A) := by
    have hrank := A.finrank_range_add_finrank_ker
    have hk : Module.finrank (ZMod 2) (Bits k) = k := by
      simpa [Bits] using (Module.finrank_fin_fun (R := ZMod 2) (n := k))
    omega
  rw [Module.card_eq_pow_finrank, h]
  norm_num

/-- Exact number of solutions for any target of any GF(2) linear map. -/
theorem fiber_count
    {k m : ℕ}
    (A : Bits k →ₗ[ZMod 2] Bits m) (t : Bits m) :
    Fintype.card {u : Bits k // A u = t} =
      if t ∈ LinearMap.range A then
        2 ^ (k - Module.finrank (ZMod 2) (LinearMap.range A))
      else 0 := by
  classical
  by_cases ht : t ∈ LinearMap.range A
  · obtain ⟨origin, h⟩ := ht
    rw [if_pos (show t ∈ LinearMap.range A from ⟨origin, h⟩)]
    exact (Fintype.card_congr (fiberEquivKer A t origin h)).trans
      (card_kernel_eq_pow A)
  · rw [if_neg ht]
    have hempty : IsEmpty {u : Bits k // A u = t} := ⟨by
      intro u
      apply ht
      exact ⟨u.val, u.property⟩⟩
    letI := hempty
    simp

/-- The external boundary merely selects the right-hand-side fiber. -/
theorem all_boundary_count
    {k m n : ℕ}
    (A : Bits k →ₗ[ZMod 2] Bits m)
    (B : Bits n →ₗ[ZMod 2] Bits m)
    (c : Bits m) (b : Bits n) :
    Fintype.card {u : Bits k // A u + B b = c} =
      if c - B b ∈ LinearMap.range A then
        2 ^ (k - Module.finrank (ZMod 2) (LinearMap.range A))
      else 0 := by
  classical
  let e : {u : Bits k // A u + B b = c} ≃
      {u : Bits k // A u = c - B b} :=
    { toFun := fun u => ⟨u.val, (add_eq_iff_eq_sub).mp u.property⟩
      invFun := fun u => ⟨u.val, (add_eq_iff_eq_sub).mpr u.property⟩
      left_inv := fun u => Subtype.ext rfl
      right_inv := fun u => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (fiber_count A (c - B b))

#print axioms IndependentETH.AffineRankNullity.fiberEquivKer
#print axioms IndependentETH.AffineRankNullity.card_kernel_eq_pow
#print axioms IndependentETH.AffineRankNullity.fiber_count
#print axioms IndependentETH.AffineRankNullity.all_boundary_count
