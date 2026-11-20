import Mathlib
import IndependentOriginalSatIncidence

/-!
# Original Anthropic literal-test incidence, expanded into Boolean wires

For the exact pinned Groundwork.SatNet.net constructor, every pair
of clusters carries a Boolean word indexed by literal slots. This
module mechanically uncurries that family of pair-local words into
one Boolean wire per (cluster-pair, literal-slot).

The permitted wire assignments are exactly the image of the source's
allowed Θ labels, not arbitrary assignments with an unproved
normalization factor. This is a bijective reindexing, preserving
individual original endpoint factors and node weights.

It prepares an OpenAI-style Boolean tensor-network interface, but
does not yet establish that OpenAI's separate clause/equality-tree
constructor produces these particular wires.
-/

namespace IndependentETH.OriginalSatNetBits

open scoped BigOperators
open Finset
open IndependentETH.SourceIncidence
open IndependentETH.OriginalSatNet

variable (φ : List (List (ℕ × Bool))) (g μ k : ℕ)

abbrev Pair := PairEdge (Fin g)
abbrev Slot := Groundwork.SatNet.Sl μ k
abbrev Wire := Pair g × Slot μ k

/-- Each source pair-local edge-label bit gets one explicit wire. -/
def uncurryLabels
    (θ : Pair g → Slot μ k → Bool) : Wire g μ k → Bool :=
  fun e => θ e.1 e.2

/-- Group per-wire bits back into the original pair-local edge labels. -/
def curryBits (bits : Wire g μ k → Bool) : Pair g → Slot μ k → Bool :=
  fun p s => bits (p, s)

theorem curry_uncurry (θ : Pair g → Slot μ k → Bool) :
    curryBits g μ k (uncurryLabels g μ k θ) = θ := by
  funext p s
  rfl

theorem uncurry_curry (bits : Wire g μ k → Bool) :
    uncurryLabels g μ k (curryBits g μ k bits) = bits := by
  funext ⟨p,s⟩
  rfl

theorem uncurry_injective :
    Function.Injective (uncurryLabels g μ k) := by
  intro a b h
  have hc := congrArg (curryBits g μ k) h
  simpa [curry_uncurry] using hc

/-- The exact source's pair-edge assignments, with no global collapse. -/
def sourceEdgeLabels : Finset (Pair g → Slot μ k → Bool) :=
  Fintype.piFinset (allowedLabels (original φ g μ k))

/-- Finite Boolean assignments to one wire per (cluster-pair, slot).
The image restriction preserves the original Θ support and padding. -/
def admissibleWires : Finset (Wire g μ k → Bool) :=
  (sourceEdgeLabels φ g μ k).image (uncurryLabels g μ k)

/-- The literal-to-wire bijection is exact, including multiplicities.
There is one Boolean wire for every pair/slot position, and source
label admissibility is preserved by the image construction. -/
theorem sum_over_source_labels
    (f : (Pair g → Slot μ k → Bool) → ℤ) :
    (∑ θ ∈ sourceEdgeLabels φ g μ k, f θ) =
      ∑ bits ∈ admissibleWires φ g μ k,
        f (curryBits g μ k bits) := by
  classical
  unfold admissibleWires
  rw [Finset.sum_image (uncurry_injective g μ k).injOn]
  simp [curry_uncurry]

/-- Original Anthropic source factors, expressed over the actual
Boolean literal-test wires; no factor is replaced or summed out. -/
def wireIncidenceValue : ℤ :=
  let N := original φ g μ k
  ∑ z ∈ Fintype.piFinset N.S,
    ∑ bits ∈ admissibleWires φ g μ k,
      (∏ a, N.W a (z a)) *
        (∏ p : Pair g,
          firstFactor N z (curryBits g μ k bits) p *
          secondFactor N z (curryBits g μ k bits) p)

/-- The *actual* SAT constructor's value equals the Boolean
pair/slot-wire contraction, preserving every cluster weight and
every endpoint equality factor. This is not an equality derived
from both encodings' final #SAT counts. -/
theorem original_value_eq_bool_wire_incidence :
    (original φ g μ k).value = wireIncidenceValue φ g μ k := by
  rw [original_value_eq_incidence]
  unfold wireIncidenceValue incidenceValue
  apply Finset.sum_congr rfl
  intro z hz
  exact sum_over_source_labels φ g μ k _

#print axioms IndependentETH.OriginalSatNetBits.sum_over_source_labels
#print axioms IndependentETH.OriginalSatNetBits.original_value_eq_bool_wire_incidence

end IndependentETH.OriginalSatNetBits
