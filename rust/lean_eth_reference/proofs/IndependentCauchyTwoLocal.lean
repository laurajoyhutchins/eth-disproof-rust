import Mathlib
import IndependentCauchySourceGrid
import IndependentCauchyTileMode

/-!
# Two-local divisibility of actual Cauchy grid differences

The October 25 Cauchy appendix needs to divide the deformation
scale α=2^(a+1) by *every nonzero integer difference* t-q in
S=[-2^a,2^a).

No rational/p-adic divisibility is postulated here. For each such
difference we construct an actual factorization

    t-q = 2^v d,   v ≤ a,   d odd.

The second theorem constructs a quotient of α by t-q in *every*
commutative ring satisfying 2^p=0. Thus the required two-local
division can be carried out even when the raw integer difference
is not a unit modulo 2^p.

Still open: combine these constructive quotient factors with the
source derivative's binomial units into the complete polynomial
C(t+αz)/(α C'(0)) over the actual source ring O and its A_p.
-/

namespace IndependentETH.CauchyTwoLocal

open IndependentETH.CauchySourceGrid
open IndependentETH.CauchyTileMode

/--
A positive integer strictly below 2^(a+1) has no factor 2^v with
v>a. This is the exact finite 2-adic decomposition needed later.
-/
theorem bounded_natural_two_factor (a n : ℕ)
    (hn : 0 < n) (hbound : n < 2 ^ (a + 1)) :
    ∃ v m : ℕ, v ≤ a ∧ Odd m ∧ n = 2 ^ v * m := by
  obtain ⟨v, m, hodd, hfactor⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hn)
  have hmpos : 0 < m := by
    have hmne : m ≠ 0 := by
      intro hm
      subst m
      simpa using hodd
    omega
  have hpowle : 2 ^ v ≤ n := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ hmpos
  have hval : v ≤ a := by
    by_contra hv
    have hle : a + 1 ≤ v := by omega
    have hpow : 2 ^ (a + 1) ≤ 2 ^ v :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mpr hle
    omega
  exact ⟨v, m, hval, hodd, hfactor⟩

/--
The integer difference for *literal* source grid points has
a bounded 2-power factor and an odd signed quotient.
-/
theorem source_difference_two_factor (a : ℕ) (t q : ℤ)
    (ht : t ∈ sourceGrid a) (hq : q ∈ sourceGrid a)
    (htq : t ≠ q) :
    ∃ v : ℕ, ∃ d : ℤ,
      v ≤ a ∧ Odd d ∧ t - q = (2 : ℤ) ^ v * d := by
  have hz : t - q ≠ 0 := sub_ne_zero.mpr htq
  have hn : 0 < (t - q).natAbs := Int.natAbs_pos.mpr hz
  have hboundZ : ((t - q).natAbs : ℤ) < sourceAlpha a := by
    simpa only [Int.abs_eq_natAbs] using
      source_difference_abs_lt_alpha a t q ht hq
  have hbound : (t - q).natAbs < 2 ^ (a + 1) := by
    have halpha : (((2 : ℕ) ^ (a + 1)) : ℤ) = sourceAlpha a := by
      simp [sourceAlpha]
    exact_mod_cast (halpha ▸ hboundZ)
  obtain ⟨v, m, hv, hm, hfactor⟩ :=
    bounded_natural_two_factor a (t - q).natAbs hn hbound
  have hfactorZ :
      ((t - q).natAbs : ℤ) = (2 : ℤ) ^ v * (m : ℤ) := by
    exact_mod_cast hfactor
  rcases le_total 0 (t - q) with hpos | hneg
  · refine ⟨v, (m : ℤ), hv, hm.natCast, ?_⟩
    calc
      t - q = ((t - q).natAbs : ℤ) :=
        (Int.natAbs_of_nonneg hpos).symm
      _ = (2 : ℤ) ^ v * (m : ℤ) := hfactorZ
  · refine ⟨v, -(m : ℤ), hv, hm.natCast.neg, ?_⟩
    have hcast : ((t - q).natAbs : ℤ) = -(t - q) := by
      simpa only [Int.natAbs_neg] using
        (Int.natAbs_of_nonneg (neg_nonneg.mpr hneg))
    calc
      t - q = -((t - q).natAbs : ℤ) := by omega
      _ = (2 : ℤ) ^ v * (-(m : ℤ)) := by rw [hfactorZ]; ring

/--
The odd integer quotient of an actual source grid difference is
a unit in every quotient where 2^p=0.
-/
theorem source_difference_odd_is_unit
    {R : Type*} [CommRing R]
    (p : ℕ) (hmod : (2 : R) ^ p = 0) (d : ℤ) (hd : Odd d) :
    IsUnit (d : R) := by
  obtain ⟨k, hk⟩ := hd
  have heq : (d : R) = 1 + (2 : R) * (k : R) := by
    rw [hk]
    push_cast
    ring
  rw [heq]
  exact one_add_even_is_unit p hmod (k : R)

/--
Construct the quotient of α by an actual nonzero difference inside
the target coefficient ring. This does not cancel an element
which may be a nonunit: it explicitly factors it as 2^v times
a *proved odd unit*.
-/
theorem source_difference_divides_alpha
    {R : Type*} [CommRing R]
    (a p : ℕ) (t q : ℤ)
    (ht : t ∈ sourceGrid a) (hq : q ∈ sourceGrid a)
    (htq : t ≠ q)
    (hmod : (2 : R) ^ p = 0) :
    ∃ w : R, ((t - q : ℤ) : R) * w = (sourceAlpha a : R) := by
  obtain ⟨v, d, hv, hd, hdiff⟩ :=
    source_difference_two_factor a t q ht hq htq
  obtain ⟨u, hu⟩ := source_difference_odd_is_unit p hmod d hd
  refine ⟨(2 : R) ^ (a + 1 - v) * ((u⁻¹ : Rˣ) : R), ?_⟩
  have he : v + (a + 1 - v) = a + 1 := by omega
  have hdiffR : ((t - q : ℤ) : R) = (2 : R) ^ v * (d : R) := by
    rw [hdiff]
    push_cast
    ring
  calc
    ((t - q : ℤ) : R) *
        ((2 : R) ^ (a + 1 - v) * ((u⁻¹ : Rˣ) : R)) =
      ((2 : R) ^ v * (2 : R) ^ (a + 1 - v)) *
        ((u : R) * ((u⁻¹ : Rˣ) : R)) := by
          rw [hdiffR, ← hu]
          ring
    _ = (2 : R) ^ (a + 1) := by rw [← pow_add, he]; simp
    _ = (sourceAlpha a : R) := by simp [sourceAlpha]

#print axioms IndependentETH.CauchyTwoLocal.bounded_natural_two_factor
#print axioms IndependentETH.CauchyTwoLocal.source_difference_two_factor
#print axioms IndependentETH.CauchyTwoLocal.source_difference_odd_is_unit
#print axioms IndependentETH.CauchyTwoLocal.source_difference_divides_alpha

end IndependentETH.CauchyTwoLocal
