import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

/-!
# Constructive signed-pair traversal from the original QueryStream source

This is a mathematical subroutine of QueryStream, not a replacement for its
signed pair callback, tuple visitor, node readout or reconstruction.

The original `QueryStreamProgram.pairs` calls
`DifferencePairsProgram.command` with the signed pair callback. The original
`DifferencePairs.fold` is a structurally recursive, finite, streaming
description of the very same admissible pair order; its correspondence with
the source-defined pair family is established in `DifferencePairs`.

Our only new operation is to instantiate that *unchanged source fold* with
additive evaluation. No assignment enumeration, table of completed pairs,
semantic #SAT oracle, or approximation is involved.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructivePairs

open scoped BigOperators
open DifferencePairs BooleanDifferences

/-- Total, executable source-ordered contraction of an additive weight.
    It visits each admissible signed pair immediately rather than constructing
    the `words` list or enumerating Boolean assignments. -/
def weightedSum {A : Type*} [AddCommMonoid A]
    (weight : List (Option Bool) → A) (n J : ℕ) : A :=
  DifferencePairs.fold (fun pair acc => acc + weight pair) n J [] 0

/-- Exact equality to the original mathematical pair-family sum.
    This reuses the upstream source fold invariant, not a second enumeration. -/
theorem weightedSum_eq_pairFamily {A : Type*} [AddCommMonoid A]
    (weight : List (Option Bool) → A) (n J : ℕ) :
    weightedSum weight n J =
      ∑ p ∈ BooleanDifferences.pairFamily n J,
        weight (DifferencePairs.encodePair p.1 p.2) := by
  have h := DifferencePairs.fold_decode_sum
    (visit := fun pair (acc : A) => acc + weight pair)
    (decode := id) (P := fun _ : A => True) (f := weight)
    (n := n) (J := J) (acc := (0 : A)) trivial
    (by
      intro pair _ acc _
      exact ⟨trivial, rfl⟩)
  simpa [weightedSum] using h.2

/-- Count callbacks of the executable source traversal. -/
def visits (n J : ℕ) : ℕ :=
  weightedSum (fun _ => (1 : ℕ)) n J

/-- Exactly one callback for each original admissible signed pair. -/
theorem visits_eq_pairCount (n J : ℕ) :
    visits n J = DifferencePairs.pairCount n J := by
  rw [visits, weightedSum_eq_pairFamily]
  simpa using (DifferencePairs.pairFamily_card n J)

/-- Once the strict support cutoff exceeds the number of coordinates, every
    ternary coordinate state is visited. This is an *exact* exponential
    cardinality, not an estimate inferred from a benchmark. -/
theorem pairCount_full_support (n J : ℕ) (hJ : n < J) :
    DifferencePairs.pairCount n J = 3 ^ n := by
  induction n generalizing J with
  | zero =>
      cases J with
      | zero => omega
      | succ J => rfl
  | succ n ih =>
      cases J with
      | zero => omega
      | succ J =>
          have hleft : n < J + 1 := by omega
          have hright : n < J := by omega
          change DifferencePairs.pairCount n (J + 1) +
            2 * DifferencePairs.pairCount n J = 3 ^ (n + 1)
          rw [ih (J + 1) hleft, ih J hright, pow_succ]
          omega

/-- The real recursive source traversal executes at least this many recursive
    visits when its support cutoff is unrestricted. -/
theorem calls_full_support_lower (n J : ℕ) (hJ : n < J) :
    3 ^ n ≤ DifferencePairs.calls n J := by
  induction n generalizing J with
  | zero =>
      cases J with
      | zero => omega
      | succ J => simp [DifferencePairs.calls]
  | succ n ih =>
      cases J with
      | zero => omega
      | succ J =>
          have hleft : n < J + 1 := by omega
          have hright : n < J := by omega
          have hl := ih (J + 1) hleft
          have hr := ih J hright
          change 3 ^ (n + 1) ≤
            1 + DifferencePairs.calls n (J + 1) + 2 * DifferencePairs.calls n J
          rw [pow_succ]
          omega

theorem visits_full_support (n J : ℕ) (hJ : n < J) :
    visits n J = 3 ^ n :=
  (visits_eq_pairCount n J).trans (pairCount_full_support n J hJ)

/-- The sign appearing in Boolean finite differences, expressed in the
    *source's* `none / some false / some true` coordinate encoding. -/
def differenceSign (pair : List (Option Bool)) : ℤ :=
  (-1 : ℤ) ^ pair.countP (fun x => x == some false)

/-- One source-derived signed sum, with no materialized pair table. -/
def signedSum (n J : ℕ) (coefficient : List (Option Bool) → ℤ) : ℤ :=
  weightedSum (fun pair => differenceSign pair * coefficient pair) n J

theorem signedSum_eq_pairFamily (n J : ℕ)
    (coefficient : List (Option Bool) → ℤ) :
    signedSum n J coefficient =
      ∑ p ∈ BooleanDifferences.pairFamily n J,
        differenceSign (DifferencePairs.encodePair p.1 p.2) *
          coefficient (DifferencePairs.encodePair p.1 p.2) := by
  exact weightedSum_eq_pairFamily _ n J

/-- The executable sign really is the original Boolean finite-difference
    sign: `some false` indexes precisely the coordinates of `E \\ U`.
    This is a local semantic theorem, not an assertion that the full
    QueryStream callback is already computable. -/
theorem differenceSign_encodePair {n : ℕ} (E U : Finset (Fin n))
    (hU : U ⊆ E) :
    differenceSign (DifferencePairs.encodePair E U) =
      (-1 : ℤ) ^ (E.card - U.card) := by
  unfold differenceSign
  congr 1
  change (DifferencePairs.encodePair E U).countP
    (fun x => x == some false) = E.card - U.card
  rw [DifferencePairs.encodePair, DifferencePairs.countP_ofFn]
  have hpoint (i : Fin n) :
      (if (if i ∈ E then some (decide (i ∈ U)) else none) == some false
        then 1 else 0 : ℕ) =
      (if i ∈ E \\ U then 1 else 0 : ℕ) := by
    by_cases hi : i ∈ E <;> by_cases hj : i ∈ U <;> simp [hi, hj]
  simp_rw [hpoint]
  rw [← Finset.card_sdiff_of_subset hU]
  simp

/-- Source-faithful signed coefficient formula with the exact exponent from
    `BooleanDifferences.difference`, rather than only a signed bit encoding. -/
theorem signedSum_eq_original_difference (n J : ℕ)
    (coefficient : List (Option Bool) → ℤ) :
    signedSum n J coefficient =
      ∑ p ∈ BooleanDifferences.pairFamily n J,
        (-1 : ℤ) ^ (p.1.card - p.2.card) *
          coefficient (DifferencePairs.encodePair p.1 p.2) := by
  rw [signedSum_eq_pairFamily]
  apply Finset.sum_congr rfl
  intro p hp
  rw [differenceSign_encodePair p.1 p.2
    (BooleanDifferences.mem_pairFamily.mp hp).2]

-- The tests exercise this pair-contraction subroutine, not QueryStream's
-- unimplemented numerical callback or a whole CNF-to-count computation.
example : visits 0 0 = 0 := by decide
example : visits 0 1 = 1 := by decide
example : visits 2 2 = 5 := by decide
example : visits 3 4 = 27 := by decide
example : signedSum 3 2 (fun _ => 1) = 1 := by decide
example : weightedSum (fun w => if w.countP Option.isSome == 1
    then (1 : ℕ) else 0) 3 2 = 6 := by decide

#eval visits 0 0
#eval visits 2 2
#eval visits 3 4
#eval signedSum 3 2 (fun _ => 1)

#print axioms weightedSum_eq_pairFamily
#print axioms pairCount_full_support
#print axioms calls_full_support_lower
#print axioms signedSum_eq_pairFamily
#print axioms differenceSign_encodePair
#print axioms signedSum_eq_original_difference

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructivePairs
