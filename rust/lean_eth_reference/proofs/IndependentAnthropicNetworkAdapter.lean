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

#print axioms IndependentETH.SourceNetwork.anthropic_value_eq_contraction
#print axioms IndependentETH.SourceNetwork.anthropic_merge_preserves_contraction
#print axioms IndependentETH.SourceNetwork.anthropic_instance_preserves_contraction

end IndependentETH.SourceNetwork
