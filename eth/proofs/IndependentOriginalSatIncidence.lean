import Mathlib
import Groundwork.SatNet
import IndependentSourceIncidence

/-!
# The actual Anthropic k-CNF constructor: incidence and factor witnesses

Source (unmodified, pinned):
  anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5
  eth/proof/machines/StepMachines/Math/SatNet.lean

This is about the original SatNet.net constructor, not a newly invented
two-node network. The constructor uses a cluster per formula block, a
boolean slot state at every literal position and one edge label per
pair of clusters, encoding all consecutive occurrence links crossing
that pair.

The equalities here expose the original link incidence and original
indicator factors individually. They do not claim that OpenAI's
October 25 clause/equality-tree network is the same graph.
-/

namespace IndependentETH.OriginalSatNet

open scoped BigOperators
open IndependentETH.SourceIncidence

variable (φ : List (List (ℕ × Bool))) (g μ k : ℕ)

/-- The actual pinned Anthropic source constructor, without a reimplementation. -/
abbrev original : Groundwork.Network (Fin g)
    (Groundwork.SatNet.Sl μ k → Bool)
    (Groundwork.SatNet.Sl μ k → Bool) :=
  Groundwork.SatNet.net φ g μ k

/-- Every source edge label is precisely the assignment of bits to the
original consecutive-occurrence links crossing that cluster pair. -/
theorem original_edge_labels (p : PairEdge (Fin g)) :
    allowedLabels (original φ g μ k) p =
      Groundwork.tuples
        (Groundwork.SatNet.Out φ p.val.1 p.val.2)
        (fun _ => Finset.univ) false := by
  have hlt : p.val.1 < p.val.2 := (Finset.mem_filter.mp p.property).2
  simp [allowedLabels, original, Groundwork.SatNet.net, hlt]

/-- The original first endpoint factor enforces the source bit
on exactly those literal slots whose next occurrence lies in b. -/
theorem original_first_factor
    (z : Fin g → Groundwork.SatNet.Sl μ k → Bool)
    (θ : PairEdge (Fin g) → Groundwork.SatNet.Sl μ k → Bool)
    (p : PairEdge (Fin g)) :
    firstFactor (original φ g μ k) z θ p =
      if ∀ s : Groundwork.SatNet.Sl μ k,
        Groundwork.SatNet.Out φ p.val.1 p.val.2 s →
          z p.val.1 s = θ p s then 1 else 0 := by
  have hlt : p.val.1 < p.val.2 := (Finset.mem_filter.mp p.property).2
  simp [firstFactor, original, Groundwork.SatNet.net, hlt]

/-- The second endpoint factor enforces precisely the original
consecutive-occurrence links coming from the first endpoint. -/
theorem original_second_factor
    (z : Fin g → Groundwork.SatNet.Sl μ k → Bool)
    (θ : PairEdge (Fin g) → Groundwork.SatNet.Sl μ k → Bool)
    (p : PairEdge (Fin g)) :
    secondFactor (original φ g μ k) z θ p =
      if ∀ s s' : Groundwork.SatNet.Sl μ k,
          Groundwork.SatNet.Link φ (p.val.1, s) (p.val.2, s') →
            z p.val.2 s' = θ p s then 1 else 0 := by
  have hlt : p.val.1 < p.val.2 := (Finset.mem_filter.mp p.property).2
  have hnot : ¬ p.val.2 < p.val.1 := not_lt_of_ge hlt.le
  simp [secondFactor, original, Groundwork.SatNet.net, hnot]

/-- The original cluster weight is not changed by incidence expansion. -/
theorem original_node_weight
    (a : Fin g) (z : Fin g → Groundwork.SatNet.Sl μ k → Bool) :
    (original φ g μ k).W a (z a) =
      Groundwork.SatNet.weight φ a (z a) := rfl

/-- Source-backed, per-incidence, factor-preserving expansion of
the *actual original Anthropic* SAT network constructor. -/
theorem original_value_eq_incidence :
    (original φ g μ k).value = incidenceValue (original φ g μ k) :=
  value_eq_incidence (original φ g μ k)

/-- The original source proves that its network counts exactly the
consistent, satisfying slot assignments. Our incidence representation
has that same value, without folding the pair labels into a global
one and without changing any local factor. -/
theorem original_incidence_eq_good :
    incidenceValue (original φ g μ k) =
      (Finset.univ.filter
        (Groundwork.SatNet.Good φ
          (g := g) (μ := μ) (k := k))).card := by
  rw [← original_value_eq_incidence]
  exact Groundwork.SatNet.value_eq_card_good

#print axioms IndependentETH.OriginalSatNet.original_value_eq_incidence
#print axioms IndependentETH.OriginalSatNet.original_incidence_eq_good

end IndependentETH.OriginalSatNet
