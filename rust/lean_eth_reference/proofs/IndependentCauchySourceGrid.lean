import Mathlib

/-!
# The original Cauchy grid, its root products and residue symmetry

Original source: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
`quantitative-contraction.tex`, section "A Cauchy deformation and
integral local coordinates".

These lemmas concern the actual source interval
S = {-2^a, ..., 2^a-1}, with α = 2^(a+1), rather than an
abstract finite root set. Every distinct integer difference between
grid points has absolute value strictly below α. The polynomial
product factorization at each root is exact in any commutative ring.

On the full residue grid modulo α, translation of differences is a
permutation, so *every* residue profile (including divisibility
profiles) has the same multiplicity at each center. What remains
unproved is the identification of the integer differences' exact
2-adic valuations with that residue profile, and extraction of the
odd derivative factor needed for the original C(T)/C'(0).

This does not assert the desired source Cauchy integrality prematurely.
-/

namespace IndependentETH.CauchySourceGrid

open scoped BigOperators

/-- The precise consecutive integer interval in the October 25 packet appendix. -/
def sourceGrid (a : ℕ) : Finset ℤ :=
  Finset.Ico (-(2 : ℤ) ^ a) ((2 : ℤ) ^ a)

/-- The original deformation scale and the size of the complete residue grid. -/
def sourceAlpha (a : ℕ) : ℤ := (2 : ℤ) ^ (a + 1)

theorem sourceGrid_mem_iff (a : ℕ) (t : ℤ) :
    t ∈ sourceGrid a ↔ -(2 : ℤ) ^ a ≤ t ∧ t < (2 : ℤ) ^ a := by
  simp [sourceGrid]

theorem zero_mem_sourceGrid (a : ℕ) : (0 : ℤ) ∈ sourceGrid a := by
  rw [sourceGrid_mem_iff]
  have hp : 0 < (2 : ℤ) ^ a := pow_pos (by norm_num) _
  constructor <;> omega

theorem sourceAlpha_eq_two_mul (a : ℕ) :
    sourceAlpha a = 2 * ((2 : ℤ) ^ a) := by
  simp [sourceAlpha, pow_succ]
  ring

theorem sourceAlpha_pos (a : ℕ) : 0 < sourceAlpha a := by
  unfold sourceAlpha
  positivity

/--
All pairwise differences lie strictly within one complete residue
period. This is needed before residue classes can determine the
actual source-grid integer valuations.
-/
theorem source_difference_abs_lt_alpha
    (a : ℕ) (t q : ℤ)
    (ht : t ∈ sourceGrid a) (hq : q ∈ sourceGrid a) :
    |t - q| < sourceAlpha a := by
  obtain ⟨htl, htu⟩ := (sourceGrid_mem_iff a t).mp ht
  obtain ⟨hql, hqu⟩ := (sourceGrid_mem_iff a q).mp hq
  rw [abs_lt, sourceAlpha_eq_two_mul]
  constructor <;> omega

/-- Enumerate the exact integer grid with its offset from -2^a. -/
def shiftedGridPoint (a : ℕ) (q : Fin (2 ^ (a + 1))) : ℤ :=
  (q.val : ℤ) - (2 : ℤ) ^ a

theorem shiftedGridPoint_mem (a : ℕ) (q : Fin (2 ^ (a + 1))) :
    shiftedGridPoint a q ∈ sourceGrid a := by
  rw [sourceGrid_mem_iff]
  have hb : (q.val : ℤ) < (2 : ℤ) ^ (a + 1) := by
    exact_mod_cast q.isLt
  have hz : 0 ≤ (q.val : ℤ) := by positivity
  have ha : (2 : ℤ) ^ (a + 1) = 2 * (2 : ℤ) ^ a := by
    rw [pow_succ]
    ring
  unfold shiftedGridPoint
  constructor <;> omega

theorem shiftedGridPoint_injective (a : ℕ) :
    Function.Injective (shiftedGridPoint a) := by
  intro q r h
  apply Fin.ext
  dsimp [shiftedGridPoint] at h
  omega

/--
Every integer in the original interval is hit exactly once. Together
with the residue-ring equivalence, this makes the original source
grid a certified complete residue system, not an assumed list.
-/
theorem shiftedGridPoint_surjective (a : ℕ) (t : ℤ)
    (ht : t ∈ sourceGrid a) :
    ∃ q : Fin (2 ^ (a + 1)), shiftedGridPoint a q = t := by
  obtain ⟨hl, hu⟩ := (sourceGrid_mem_iff a t).mp ht
  have hN : (2 : ℤ) ^ (a + 1) = 2 * (2 : ℤ) ^ a := by
    rw [pow_succ]
    ring
  have hzero : 0 ≤ t + (2 : ℤ) ^ a := by omega
  have htop : t + (2 : ℤ) ^ a < (2 : ℤ) ^ (a + 1) := by omega
  have hc : (((2 : ℕ) ^ (a + 1) : ℕ) : ℤ) =
      (2 : ℤ) ^ (a + 1) := by norm_cast
  have hnat : (t + (2 : ℤ) ^ a).toNat < (2 : ℕ) ^ (a + 1) := by
    have heq : (((t + (2 : ℤ) ^ a).toNat : ℕ) : ℤ) =
        t + (2 : ℤ) ^ a := Int.toNat_of_nonneg hzero
    omega
  refine ⟨⟨(t + (2 : ℤ) ^ a).toNat, hnat⟩, ?_⟩
  unfold shiftedGridPoint
  have heq : (((t + (2 : ℤ) ^ a).toNat : ℕ) : ℤ) =
      t + (2 : ℤ) ^ a := Int.toNat_of_nonneg hzero
  omega

/-- A bijective enumeration of the literal integer source grid. -/
noncomputable def sourceGridFinEquiv (a : ℕ) :
    Fin (2 ^ (a + 1)) ≃ {t : ℤ // t ∈ sourceGrid a} := by
  classical
  let F : Fin (2 ^ (a + 1)) → {t : ℤ // t ∈ sourceGrid a} :=
    fun q => ⟨shiftedGridPoint a q, shiftedGridPoint_mem a q⟩
  apply Equiv.ofBijective F
  constructor
  · intro q r h
    apply shiftedGridPoint_injective a
    exact congrArg Subtype.val h
  · intro ⟨t, ht⟩
    obtain ⟨q, hq⟩ := shiftedGridPoint_surjective a t ht
    refine ⟨q, ?_⟩
    exact Subtype.ext hq

/-- The literal source grid is equivalent to one complete residue ring. -/
noncomputable def sourceGridResidueEquiv (a : ℕ) :
    {t : ℤ // t ∈ sourceGrid a} ≃ ZMod (2 ^ (a + 1)) := by
  letI : NeZero (2 ^ (a + 1)) := ⟨by positivity⟩
  exact (sourceGridFinEquiv a).symm.trans (ZMod.finEquiv (2 ^ (a + 1))).toEquiv

/--
The Cauchy numerator as the source's finite product, evaluated
inside an arbitrary commutative ring.
-/
def cauchyProduct {R : Type*} [CommRing R]
    (a : ℕ) (T : R) : R :=
  ∏ q ∈ sourceGrid a, (T - (q : R))

/--
At any grid point t, the exact product factors out its vanishing
term αζ. This is the source-level algebraic input to numerator
normalization; it does not divide by C'(0).
-/
theorem cauchy_product_at_grid_point
    {R : Type*} [CommRing R]
    (a : ℕ) (t : ℤ) (ht : t ∈ sourceGrid a)
    (z : R) :
    cauchyProduct a ((t : R) + (sourceAlpha a : R) * z) =
      (sourceAlpha a : R) * z *
        ∏ q ∈ (sourceGrid a).erase t,
          ((t : R) - (q : R) + (sourceAlpha a : R) * z) := by
  unfold cauchyProduct
  have hprod := Finset.mul_prod_erase (sourceGrid a)
    (fun q : ℤ => ((t : R) + (sourceAlpha a : R) * z) - (q : R)) ht
  calc
    ((sourceGrid a).prod (fun q : ℤ => ((t : R) + (sourceAlpha a : R) * z) - (q : R))) =
        (((t : R) + (sourceAlpha a : R) * z) - (t : R)) *
          ∏ q ∈ (sourceGrid a).erase t,
            (((t : R) + (sourceAlpha a : R) * z) - (q : R)) :=
      hprod.symm
    _ = (sourceAlpha a : R) * z *
          ∏ q ∈ (sourceGrid a).erase t,
            ((t : R) - (q : R) + (sourceAlpha a : R) * z) := by
      congr 1
      · ring
      · apply Finset.prod_congr rfl
        intro q _
        ring

/-- The exact, undivided source derivative product at the center zero. -/
def sourceDerivativeAtZero (a : ℕ) : ℤ :=
  ∏ q ∈ (sourceGrid a).erase 0, -q

theorem sourceDerivativeAtZero_ne_zero (a : ℕ) :
    sourceDerivativeAtZero a ≠ 0 := by
  unfold sourceDerivativeAtZero
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have hne : q ≠ 0 := (Finset.mem_erase.mp hq).1
  simpa using hne

/--
The residue-grid difference map at each center is an involution.
Consequently no class, valuation class, or weighted residue profile
can be favored by translating the chosen grid point.
-/
def residueDifferenceEquiv
    {N : ℕ} (t : ZMod N) : ZMod N ≃ ZMod N where
  toFun := fun q => t - q
  invFun := fun r => t - r
  left_inv := by
    intro q
    dsimp
    abel
  right_inv := by
    intro r
    dsimp
    abel

theorem residue_difference_profile_uniform
    (a : ℕ) (t : ZMod (2 ^ (a + 1)))
    (profile : ZMod (2 ^ (a + 1)) → ℕ) :
    (∑ q : ZMod (2 ^ (a + 1)), profile (t - q)) =
      ∑ r : ZMod (2 ^ (a + 1)), profile r := by
  classical
  exact Equiv.sum_comp (residueDifferenceEquiv t) profile

/--
At any center, exactly the same number of residues have differences
divisible by 2^k. No probability or independence assumption is used.
-/
theorem residue_difference_divisibility_count
    (a k : ℕ) (t : ZMod (2 ^ (a + 1))) :
    ((Finset.univ : Finset (ZMod (2 ^ (a + 1)))).filter
      (fun q => ∃ u : ZMod (2 ^ (a + 1)),
        t - q = (2 : ZMod (2 ^ (a + 1))) ^ k * u)).card =
    ((Finset.univ : Finset (ZMod (2 ^ (a + 1)))).filter
      (fun r => ∃ u : ZMod (2 ^ (a + 1)),
        r = (2 : ZMod (2 ^ (a + 1))) ^ k * u)).card := by
  classical
  have h := residue_difference_profile_uniform a t
    (fun r => if ∃ u : ZMod (2 ^ (a + 1)),
        r = (2 : ZMod (2 ^ (a + 1))) ^ k * u then (1 : ℕ) else 0)
  simpa [Finset.sum_ite] using h

#print axioms IndependentETH.CauchySourceGrid.zero_mem_sourceGrid
#print axioms IndependentETH.CauchySourceGrid.shiftedGridPoint_mem
#print axioms IndependentETH.CauchySourceGrid.shiftedGridPoint_injective
#print axioms IndependentETH.CauchySourceGrid.shiftedGridPoint_surjective
#print axioms IndependentETH.CauchySourceGrid.sourceGridFinEquiv
#print axioms IndependentETH.CauchySourceGrid.sourceGridResidueEquiv
#print axioms IndependentETH.CauchySourceGrid.source_difference_abs_lt_alpha
#print axioms IndependentETH.CauchySourceGrid.cauchy_product_at_grid_point
#print axioms IndependentETH.CauchySourceGrid.sourceDerivativeAtZero_ne_zero
#print axioms IndependentETH.CauchySourceGrid.residue_difference_profile_uniform
#print axioms IndependentETH.CauchySourceGrid.residue_difference_divisibility_count

end IndependentETH.CauchySourceGrid
