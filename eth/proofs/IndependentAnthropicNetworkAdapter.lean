import Mathlib
import Groundwork.Net.Net

/-!
# Original Anthropic network semantics as a common factor contraction

The imported files Groundwork/Net/{Defs,Calculus,Net}.lean are unmodified from
anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

The source Network.value, Network.merge, Network.value_merge, Network.Z_toInst,
and Inst.Z declarations are reused exactly. This module does not claim the
OpenAI packet algorithm is identical to Anthropic grouping.
-/

namespace IndependentETH.SourceNetwork

open scoped BigOperators
open Finset

/--
Finite node-state contraction with pair interactions expanded into a
finite sum over shared edge labels. Parameters are actual input factor
tables, not a presumed source-value function.
-/
def contraction
    {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (states : J → Finset σ)
    (nodeWeight : J → σ → ℤ)
    (edgeLabels : J → J → Finset τ)
    (edgeFactor : J → J → σ → τ → ℤ) : ℤ :=
  ∑ z ∈ Fintype.piFinset states,
    (∏ a, nodeWeight a (z a)) *
      ∏ pair ∈ Groundwork.pairs J,
        ∑ label ∈ edgeLabels (min pair.1 pair.2) (max pair.1 pair.2),
          edgeFactor pair.1 pair.2 (z pair.1) label *
            edgeFactor pair.2 pair.1 (z pair.2) label

/-- The pinned Anthropic network definition is the common contraction. -/
theorem anthropic_value_eq_contraction
    {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) :
    N.value = contraction N.S N.W N.Θ N.f := by
  rfl

/--
Node regrouping preserves this common value. The nontrivial proof is
Groundwork.Network.value_merge from the exact pinned source.
-/
theorem anthropic_merge_preserves_contraction
    {J J' σ τ : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ) (color : J → J')
    (outsideState : σ) (outsideLabel : τ) :
    contraction (N.merge color outsideState outsideLabel).S
      (N.merge color outsideState outsideLabel).W
      (N.merge color outsideState outsideLabel).Θ
      (N.merge color outsideState outsideLabel).f =
    contraction N.S N.W N.Θ N.f := by
  change (N.merge color outsideState outsideLabel).value = N.value
  exact Groundwork.Network.value_merge N color outsideState outsideLabel

/--
The source instance routing to one label per edge preserves the common
value under the original source's explicit per-pair label bijection.
-/
theorem anthropic_instance_preserves_contraction
    {J σ τ A : Type*} [Fintype J] [LinearOrder J]
    [Fintype A] [DecidableEq A]
    (N : Groundwork.Network J σ τ)
    (labelCodes : J → J → Finset A)
    (decode : J → J → A → τ)
    (hcode : ∀ a b, a < b →
      Set.BijOn (decode a b) (labelCodes a b) (N.Θ a b))
    (defaultCode : A) :
    (N.toInst labelCodes decode).Z defaultCode =
      contraction N.S N.W N.Θ N.f := by
  calc
    (N.toInst labelCodes decode).Z defaultCode = N.value :=
      Groundwork.Network.Z_toInst N labelCodes decode hcode defaultCode
    _ = contraction N.S N.W N.Θ N.f :=
      anthropic_value_eq_contraction N

/--
The source's node grouping followed by its finite-alphabet instance
construction preserves its *original* network value in one statement.
Both transformations are the exact pinned Anthropic definitions.
-/
theorem anthropic_grouped_instance_eq_original
    {J J' σ τ A : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    [Fintype A] [DecidableEq A]
    (N : Groundwork.Network J σ τ) (color : J → J')
    (outsideState : σ) (outsideLabel : τ)
    (labelCodes : J' → J' → Finset A)
    (decode : J' → J' → A → (J × J → τ))
    (hcode : ∀ a b, a < b →
      Set.BijOn (decode a b) (labelCodes a b)
        ((N.merge color outsideState outsideLabel).Θ a b))
    (defaultCode : A) :
    ((N.merge color outsideState outsideLabel).toInst labelCodes decode).Z
      defaultCode = N.value := by
  calc
    ((N.merge color outsideState outsideLabel).toInst labelCodes decode).Z
        defaultCode =
      contraction (N.merge color outsideState outsideLabel).S
        (N.merge color outsideState outsideLabel).W
        (N.merge color outsideState outsideLabel).Θ
        (N.merge color outsideState outsideLabel).f :=
      anthropic_instance_preserves_contraction
        (N.merge color outsideState outsideLabel) labelCodes decode hcode defaultCode
    _ = contraction N.S N.W N.Θ N.f :=
      anthropic_merge_preserves_contraction N color outsideState outsideLabel
    _ = N.value := (anthropic_value_eq_contraction N).symm

/--
A two-node source network with one allowed edge label and one joint
assignment. Every local weight is one, so its exact value is one.
-/
private def oneEdgeNetwork : Groundwork.Network (Fin 2) Bool Bool where
  S _ := {false}
  W _ _ := 1
  Θ _ _ := {true}
  f _ _ _ _ := 1
  c _ _ := 1

/--
Not every nominal edge-code mapping preserves value. Dropping all edge
codes removes the only contributing edge label, changing 1 to 0.
The failed bijection cannot be omitted from the source adapter.
-/
theorem dropping_edge_labels_changes_value :
    (oneEdgeNetwork.toInst
      (fun _ _ => (∅ : Finset Bool))
      (fun _ _ _ => true)).Z false ≠ oneEdgeNetwork.value := by
  decide

#print axioms IndependentETH.SourceNetwork.anthropic_value_eq_contraction
#print axioms IndependentETH.SourceNetwork.anthropic_merge_preserves_contraction
#print axioms IndependentETH.SourceNetwork.anthropic_instance_preserves_contraction
#print axioms IndependentETH.SourceNetwork.anthropic_grouped_instance_eq_original
#print axioms IndependentETH.SourceNetwork.dropping_edge_labels_changes_value

end IndependentETH.SourceNetwork
