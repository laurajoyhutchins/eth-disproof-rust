import Mathlib

/-!
# Orbit-sparse packet bounds and finite conditional expectation

This module isolates kernel-checkable finite arithmetic used by the
simultaneous matching-class / port-labeling research. It does not assert
that the original source's modified Cauchy deformation, weighted modes,
or complete two-adic recursion are proved.

The sources are the original appendix's quantitative-contraction.tex
and research/two-adic-simultaneous-potential.md. The probabilistic
matching/port moment estimates and the source-specific orbit partition
remain separate proof obligations.

In this module, `s` is a finite set of occupied signatures,
`classes` counts ordered classes in each orbit,
`load` bounds the maximum ordered class load in each orbit,
and `packet` is its packet count.
-/

namespace TwoAdicJointPotential

open scoped BigOperators

/-- The exact integer waste identity is equivalent to the source packet cap. -/
theorem packet_cap_iff_waste
    (M L P imbalance rounding : ℕ)
    (hslots : L * P = M + imbalance + rounding) :
    L * P ≤ 3 * M ↔ imbalance + rounding ≤ 2 * M := by
  omega

/-- Independently bounded real row/column ports bound each child incidence. -/
theorem child_bound_from_two_ports
    (M r rowPorts columnPorts childEdges : ℕ)
    (hrow : r * rowPorts ≤ 3 * M)
    (hcol : r * columnPorts ≤ 3 * M)
    (hchild : childEdges ≤ rowPorts + columnPorts) :
    r * childEdges ≤ 6 * M := by
  calc
    r * childEdges ≤ r * (rowPorts + columnPorts) :=
      Nat.mul_le_mul_left r hchild
    _ = r * rowPorts + r * columnPorts := Nat.mul_add r rowPorts columnPorts
    _ ≤ 3 * M + 3 * M := Nat.add_le_add hrow hcol
    _ = 6 * M := by omega

/--
For every nonempty finite set of candidate labels, if the average
conditional score equals the old potential, at least one candidate
has score no larger than the old potential. The theorem works for
exact rational potentials with any sign, not merely nonnegative data.
-/
theorem exists_nonincreasing_choice
    {α : Type*} [DecidableEq α]
    (candidates : Finset α) (hne : candidates.Nonempty)
    (score : α → ℚ) (prior : ℚ)
    (hmean :
      (∑ x ∈ candidates, score x) =
        (candidates.card : ℚ) * prior) :
    ∃ x ∈ candidates, score x ≤ prior := by
  classical
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image candidates score hne
  refine ⟨x, hx, ?_⟩
  have hsum :
      (candidates.card : ℚ) * score x ≤
        ∑ y ∈ candidates, score y := by
    calc
      (candidates.card : ℚ) * score x =
          ∑ y ∈ candidates, score x := by simp
      _ ≤ ∑ y ∈ candidates, score y := by
        exact Finset.sum_le_sum (by
          intro y hy
          exact hmin y hy)
  have hcard : (0 : ℚ) < (candidates.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [hmean] at hsum
  nlinarith

/--
The actual coordinatewise-swap orbit key for ordered symbol pairs.
It is deliberately given in source-facing `Fin a → Fin r × Fin r`
notation, so the next proof can count the real fibers of this map.
-/
def coordinateUnorderedSignature (r a : ℕ)
    (ordered : Fin a → Fin r × Fin r) : Fin a → Fin r × Fin r :=
  fun i =>
    (min (ordered i).1 (ordered i).2,
      max (ordered i).1 (ordered i).2)

/--
Every ordered pair-label class belongs to exactly one coordinatewise
unordered signature. This is a concrete finite orbit partition,
not merely an assumed abstract class-count equality.
-/
theorem ordered_classes_partitioned_by_signature (r a : ℕ) :
    (∑ signature ∈
        ((Finset.univ : Finset (Fin a → Fin r × Fin r)).image
          (coordinateUnorderedSignature r a)),
      ((Finset.univ : Finset (Fin a → Fin r × Fin r)).filter
        (fun ordered => coordinateUnorderedSignature r a ordered = signature)).card) =
      (r * r) ^ a := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin a → Fin r × Fin r)).card := by
      symm
      exact Finset.card_eq_sum_card_image
        (coordinateUnorderedSignature r a) Finset.univ
    _ = (r * r) ^ a := by
      simp [Fintype.card_fun, Fintype.card_prod]

/-- The concrete orbit partition has exactly `D = r^(2a)` classes. -/
theorem ordered_classes_partitioned_source_D (r a : ℕ) :
    (∑ signature ∈
        ((Finset.univ : Finset (Fin a → Fin r × Fin r)).image
          (coordinateUnorderedSignature r a)),
      ((Finset.univ : Finset (Fin a → Fin r × Fin r)).filter
        (fun ordered => coordinateUnorderedSignature r a ordered = signature)).card) =
      r ^ (2 * a) := by
  rw [ordered_classes_partitioned_by_signature]
  rw [mul_pow, ← pow_mul]
  ring

/--
An abstract orbit-sum lemma. It deliberately assumes the geometric
facts `sum classes = D` and `L * packets ≤ classes * load + L`.
Those premises must be transported from the actual finite slot
construction before this lemma can certify the source recursion.

Its conclusion is the specific `PL ≤ 3M` source packet bound.
-/
theorem orbit_packet_budget
    {ι : Type*} [DecidableEq ι]
    (orbits : Finset ι)
    (classes packet : ι → ℚ)
    (M L D k t upper : ℚ)
    (hD : 0 < D)
    (hclasses : (∑ i ∈ orbits, classes i) = D)
    (hclass_nonneg : ∀ i ∈ orbits, 0 ≤ classes i)
    (hper_orbit :
      ∀ i ∈ orbits,
        L * packet i ≤ classes i * upper + L)
    (hupper : 2 * D * upper = 3 * M + 2 * D * k * t)
    (hbudget :
      2 * (k * D * t + L * (orbits.card : ℚ)) ≤ 3 * M) :
    L * (∑ i ∈ orbits, packet i) ≤ 3 * M := by
  have hsum :
      L * (∑ i ∈ orbits, packet i) ≤
        ∑ i ∈ orbits, (classes i * upper + L) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (by
      intro i hi
      exact hper_orbit i hi)
  have hcount :
      (∑ i ∈ orbits, (classes i * upper + L)) =
        D * upper + L * (orbits.card : ℚ) := by
    calc
      (∑ i ∈ orbits, (classes i * upper + L)) =
          (∑ i ∈ orbits, classes i * upper) +
            (∑ _i ∈ orbits, L) := by rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ orbits, classes i) * upper +
          (orbits.card : ℚ) * L := by
        simp [← Finset.sum_mul]
      _ = D * upper + L * (orbits.card : ℚ) := by
        rw [hclasses]
        ring
  have hlinear :
      D * upper = 3 * M / 2 + k * D * t := by
    nlinarith [hupper]
  rw [hcount, hlinear] at hsum
  nlinarith [hbudget]

/-- The number of occupied orbits is never larger than all possible orbits. -/
theorem replace_occupied_by_all_orbits
    (M L D k t : ℚ) (occupied allOrbits : ℕ)
    (hcount : occupied ≤ allOrbits)
    (hbound :
      2 * (k * D * t + L * (allOrbits : ℚ)) ≤ 3 * M)
    (hL : 0 ≤ L) :
    2 * (k * D * t + L * (occupied : ℚ)) ≤ 3 * M := by
  have hnat : (occupied : ℚ) ≤ (allOrbits : ℚ) := by
    exact_mod_cast hcount
  nlinarith

#print axioms TwoAdicJointPotential.packet_cap_iff_waste
#print axioms TwoAdicJointPotential.child_bound_from_two_ports
#print axioms TwoAdicJointPotential.exists_nonincreasing_choice
#print axioms TwoAdicJointPotential.ordered_classes_partitioned_by_signature
#print axioms TwoAdicJointPotential.ordered_classes_partitioned_source_D
#print axioms TwoAdicJointPotential.orbit_packet_budget
#print axioms TwoAdicJointPotential.replace_occupied_by_all_orbits

end TwoAdicJointPotential
