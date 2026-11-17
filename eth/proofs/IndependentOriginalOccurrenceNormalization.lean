import Mathlib
import Groundwork.SatNet
import IndependentOriginalSatIncidence

/-!
# Original Anthropic consecutive-occurrence links versus global copy equality

In the original source Groundwork.SatNet.net, equalities connect each
literal occurrence to the *next* occurrence of the same variable.
The OpenAI October 25 clause/equality-tree construction uses an
equality tree on copies of each variable. Both are intended to impose
a single Boolean choice on all occurrences.

Here we prove, from the actual pinned SatNet.Consec and SatNet.Link
definitions, that its local link equalities are exactly equivalent
to the global common-variable equality predicate. This is a
pointwise (factor-level) theorem, not just agreement of final counts.
No equality-tree topology from the October 25 manuscript is assumed
to have been implemented or verified by this theorem.
-/

namespace IndependentETH.OriginalOccurrence

open scoped BigOperators
open Groundwork.SatNet

variable (φ : List (List (ℕ × Bool))) (g μ k : ℕ)

abbrev Occ := Groundwork.SatNet.Slot g μ k

/-- Nonempty occurrences of the same source variable. -/
def SameVariable (p q : Occ g μ k) : Prop :=
  lab φ p ≠ none ∧ lab φ p = lab φ q

/-- The canonical global constraint after contracting equality wires. -/
def AllCopiesEqual (z : Fin g → Sl μ k → Bool) : Prop :=
  ∀ p q : Occ g μ k, SameVariable φ g μ k p q →
    z p.1 p.2 = z q.1 q.2

/-- The actual original consecutive-occurrence tests constrain the
same bits as complete equality of every pair of occurrences of each
variable. This uses SatNet.eq_of_consec from pinned source. -/
theorem source_chain_iff_global (z : Fin g → Sl μ k → Bool) :
    (∀ p q : Occ g μ k, Link φ p q →
       z p.1 p.2 = z q.1 q.2) ↔
      AllCopiesEqual φ g μ k z := by
  constructor
  · intro h p q hpq
    exact eq_of_consec idx_injective
      (fun p q hpq => h p q hpq) hpq.1 hpq.2
  · intro h p q hpq
    exact h p q ⟨hpq.2.1, hpq.2.2.1⟩

/-- A clause check plus empty-slot padding and global agreement
is the source-independent occurrence-level contraction predicate. -/
def OccurrenceNormalForm (z : Fin g → Sl μ k → Bool) : Prop :=
  (∀ p : Occ g μ k, lit φ p = none → z p.1 p.2 = false) ∧
  (∀ (a : Fin g) (c : Fin μ), a.val * μ + c.val < φ.length →
    ∃ j : Fin k, (lit φ (a, c, j)).map Prod.snd =
      some (z a (c, j))) ∧
  AllCopiesEqual φ g μ k z

/-- The original SAT constructor's Good predicate is precisely the
common occurrence-level clause/equality normal form, for every
formula including duplicate literals and empty slots. -/
theorem source_good_iff_normal (z : Fin g → Sl μ k → Bool) :
    Good φ z ↔ OccurrenceNormalForm φ g μ k z := by
  unfold Good OccurrenceNormalForm
  exact and_congr Iff.rfl
    (and_congr Iff.rfl (source_chain_iff_global φ g μ k z))

/-- Exact factor-level identity: the product of the original
Anthropic node weights and pair interactions equals the indicator
of the canonical occurrence normal form, term by term. -/
theorem original_factor_term_eq_normal (z : Fin g → Sl μ k → Bool) :
    (∏ a, (net φ g μ k).W a (z a)) *
      (∏ p ∈ Groundwork.pairs (Fin g),
        (net φ g μ k).Ψ p.1 p.2 (z p.1) (z p.2)) =
      (if OccurrenceNormalForm φ g μ k z then (1 : ℤ) else 0) := by
  rw [Groundwork.SatNet.term_eq]
  exact congrArg (fun p : Prop => if p then (1 : ℤ) else 0)
    (propext (source_good_iff_normal φ g μ k z))

#print axioms IndependentETH.OriginalOccurrence.source_chain_iff_global
#print axioms IndependentETH.OriginalOccurrence.source_good_iff_normal
#print axioms IndependentETH.OriginalOccurrence.original_factor_term_eq_normal

end IndependentETH.OriginalOccurrence
