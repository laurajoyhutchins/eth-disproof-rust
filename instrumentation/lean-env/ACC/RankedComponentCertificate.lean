import Mathlib
import ACC.EqualityCertificate

/-!
# Locally checkable ranked-parent certificates for equality components

A spanning-path condition on arbitrary labels can be replaced by local
checks if every nonroot vertex carries a source-edge parent whose natural
rank strictly decreases. Strong induction on rank establishes a source
path to the designated root of that label. This excludes cycles without
performing transitive closure during verification.

The Lean theorem covers the mathematical certificate contract and its
Boolean decision procedure; it is not a compiler-level refinement of Rust.
-/

namespace ACC.RankedComponentCertificate

open scoped BigOperators
open ACC.EqualityCertificate
open ACC.EqualityComponents
open ACC.EqualityEdgeClosure

variable {I C : Type*}

/-- All conditions are local checks of a vertex, a class root or a
    source edge; none require a global reachability query. -/
structure RankedConditions
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ) : Prop where
  source_closed : ∀ e ∈ edges, label e.1 = label e.2
  root_label : ∀ c, label (root c) = c
  root_none : ∀ c, parent (root c) = none
  root_zero : ∀ c, rank (root c) = 0
  none_is_root : ∀ i, parent i = none → i = root (label i)
  parent_edge : ∀ i p, parent i = some p →
    (i, p) ∈ edges ∨ (p, i) ∈ edges
  parent_label : ∀ i p, parent i = some p →
    label p = label i
  parent_decreases : ∀ i p, parent i = some p →
    rank p < rank i

/-- A decreasing source-edge parent chain reaches the asserted root.
    The induction does not trust a DSU forest or a graph-search result. -/
theorem connected_to_declared_root
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (h : RankedConditions edges label root parent rank)
    (i : I) :
    EdgeConnected edges i (root (label i)) := by
  have aux : ∀ k : ℕ, ∀ j : I, rank j = k →
      EdgeConnected edges j (root (label j)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hrank
      cases hp : parent j with
      | none =>
          have hroot : j = root (label j) := h.none_is_root j hp
          rw [hroot]
          exact Relation.EqvGen.refl _
      | some p =>
          have hstep : EdgeConnected edges j p := by
            rcases h.parent_edge j p hp with hf | hr
            · exact Relation.EqvGen.rel _ _ hf
            · exact Relation.EqvGen.symm _ _
                (Relation.EqvGen.rel _ _ hr)
          have hlt : rank p < k := by
            calc
              rank p < rank j := h.parent_decreases j p hp
              _ = k := hrank
          have hpRoot : EdgeConnected edges p (root (label p)) :=
            ih (rank p) hlt p rfl
          rw [h.parent_label j p hp] at hpRoot
          exact Relation.EqvGen.trans _ _ _ hstep hpRoot
  exact aux (rank i) i rfl

/-- The local ranked-parent conditions *suffice* to establish the exact
    edge-connected component equivalence. -/
theorem label_eq_iff_connected
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (h : RankedConditions edges label root parent rank)
    (a b : I) :
    label a = label b ↔ EdgeConnected edges a b := by
  constructor
  · intro hab
    have ha := connected_to_declared_root edges label root parent rank h a
    have hb := connected_to_declared_root edges label root parent rank h b
    rw [hab] at ha
    exact Relation.EqvGen.trans _ _ _ ha
      (Relation.EqvGen.symm _ _ hb)
  · intro hab
    exact connected_same_label edges label h.source_closed hab

/-- Local ranked-parent evidence discharges the earlier global spanning
    hypothesis, using the original edge list as the certified supergraph. -/
theorem ranked_to_conditions
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (h : RankedConditions edges label root parent rank) :
    Conditions edges edges label := by
  refine ⟨?_, h.source_closed, ?_⟩
  · intro e he
    exact he
  · intro a b hab
    exact (label_eq_iff_connected edges label root parent rank h a b).mp hab

/-- The exact source-edge contraction can be evaluated by the labels in
    any locally valid ranked-parent certificate. -/
theorem ranked_contraction
    [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (h : RankedConditions edges label root parent rank)
    (weight : I → Bool → ℤ) :
    (∑ x : {x : I → Bool // ∀ e ∈ edges, x e.1 = x e.2},
      ∏ i : I, weight i (x.1 i)) =
    ∏ c : C, ∑ bit : Bool,
      ∏ i ∈ (Finset.univ : Finset I) with label i = c,
        weight i bit := by
  classical
  apply certified_contraction edges edges label
    (ranked_to_conditions edges label root parent rank h)
  intro c
  exact ⟨root c, h.root_label c⟩

/-- A deliberately simple finite Boolean specification of the local
    guard conditions. Its correctness is proved below; its evaluation
    complexity is not claimed to match the Rust loops. -/
def checkRanked
    [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ) : Bool :=
  decide (∀ e ∈ edges, label e.1 = label e.2) &&
  decide (∀ c, label (root c) = c) &&
  decide (∀ c, parent (root c) = none) &&
  decide (∀ c, rank (root c) = 0) &&
  decide (∀ i, parent i = none → i = root (label i)) &&
  decide (∀ i p, parent i = some p →
    (i, p) ∈ edges ∨ (p, i) ∈ edges) &&
  decide (∀ i p, parent i = some p → label p = label i) &&
  decide (∀ i p, parent i = some p → rank p < rank i)

/-- Soundness of the actual Lean Boolean guard specification. The proof
    does not merely assume RankedConditions as an opaque hypothesis. -/
theorem checkRanked_sound
    [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (h : checkRanked edges label root parent rank = true) :
    RankedConditions edges label root parent rank := by
  simp only [checkRanked, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2,
    h.1.1.2, h.1.2, h.2⟩

/-- An accepted Boolean certificate implies exact source contraction. -/
theorem checked_ranked_contraction
    [Fintype I] [Fintype C] [DecidableEq I] [DecidableEq C]
    (edges : List (I × I))
    (label : I → C) (root : C → I)
    (parent : I → Option I) (rank : I → ℕ)
    (weight : I → Bool → ℤ)
    (h : checkRanked edges label root parent rank = true) :
    (∑ x : {x : I → Bool // ∀ e ∈ edges, x e.1 = x e.2},
       ∏ i : I, weight i (x.1 i)) =
    ∏ c : C, ∑ bit : Bool,
      ∏ i ∈ (Finset.univ : Finset I) with label i = c,
        weight i bit := by
  exact ranked_contraction edges label root parent rank
    (checkRanked_sound edges label root parent rank h) weight

#print axioms ACC.RankedComponentCertificate.connected_to_declared_root
#print axioms ACC.RankedComponentCertificate.label_eq_iff_connected
#print axioms ACC.RankedComponentCertificate.ranked_contraction
#print axioms ACC.RankedComponentCertificate.checkRanked_sound
#print axioms ACC.RankedComponentCertificate.checked_ranked_contraction

end ACC.RankedComponentCertificate
