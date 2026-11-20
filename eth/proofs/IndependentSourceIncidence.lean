import Mathlib
import Groundwork.Net.Net

/-!
# Incidence-exact expansion of the pinned Anthropic source network

The input is the unchanged original Groundwork.Network:
  S a, W a z, Theta a b, f a b z theta.
A label variable is indexed by *each original unordered node pair*;
its allowed set is exactly Theta a b. No pair labels are collapsed
into one global label, and no local factor is re-evaluated or replaced.

This gives the shared finite factor-network normal form needed before
a Boolean bipartite realization. It does not yet prove that either
algorithm's separate SAT-to-network constructor produces the other's
encoding, nor does it bit-encode variable-length Theta label words.
-/

namespace IndependentETH.SourceIncidence

open scoped BigOperators
open Finset

/-- The original source's unordered pair set, as a finite edge type. -/
abbrev PairEdge (J : Type*) [Fintype J] [LinearOrder J] :=
  (Groundwork.pairs J : Finset (J × J))

/-- Exactly the original source label set, indexed by an actual pair. -/
def allowedLabels {J σ τ : Type*}
    [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) (p : PairEdge J) : Finset τ :=
  N.Θ p.val.1 p.val.2

/-- Original incidence on the first endpoint of an unordered pair. -/
def firstIncident {J : Type*} [Fintype J] [LinearOrder J]
    (p : PairEdge J) (a : J) : Prop := p.val.1 = a

/-- Original incidence on the second endpoint of an unordered pair. -/
def secondIncident {J : Type*} [Fintype J] [LinearOrder J]
    (p : PairEdge J) (a : J) : Prop := p.val.2 = a

/-- The unchanged source factor at the first endpoint of the edge. -/
def firstFactor {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ)
    (z : J → σ) (θ : (p : PairEdge J) → τ) (p : PairEdge J) : ℤ :=
  N.f p.val.1 p.val.2 (z p.val.1) (θ p)

/-- The unchanged source factor at the second endpoint of the edge. -/
def secondFactor {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ)
    (z : J → σ) (θ : (p : PairEdge J) → τ) (p : PairEdge J) : ℤ :=
  N.f p.val.2 p.val.1 (z p.val.2) (θ p)

/-- Normal form: independent node settings and one independent label
for each original pair, with the original endpoint-specific factors.
This is an incidence-preserving translation, not merely a scalar oracle. -/
def incidenceValue {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) : ℤ :=
  ∑ z ∈ Fintype.piFinset N.S,
    ∑ θ ∈ Fintype.piFinset (allowedLabels N),
      (∏ a, N.W a (z a)) *
        (∏ p : PairEdge J, firstFactor N z θ p * secondFactor N z θ p)

/-- Each individual pair contribution is unchanged, including signs,
zero factors, multiplicities and all of the original label choices. -/
private theorem source_pair_expansion
    {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) (z : J → σ)
    (p : PairEdge J) :
    N.Ψ p.val.1 p.val.2 (z p.val.1) (z p.val.2) =
      ∑ θ ∈ allowedLabels N p,
        N.f p.val.1 p.val.2 (z p.val.1) θ *
        N.f p.val.2 p.val.1 (z p.val.2) θ := by
  have hlt : p.val.1 < p.val.2 := by
    exact (Finset.mem_filter.mp p.property).2
  simp [Groundwork.Network.Ψ, Groundwork.Network.lab,
    allowedLabels, hlt.le]

/-- Original source Network.value is *exactly* the incidence-indexed
factor contraction, for every finite source network. No restriction on
the node states, label alphabets, graph shape, signed entries or zeros. -/
theorem value_eq_incidence
    {J σ τ : Type*} [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) :
    N.value = incidenceValue N := by
  classical
  unfold Groundwork.Network.value incidenceValue
  apply Finset.sum_congr rfl
  intro z hz
  have hp :
      (∏ p ∈ Groundwork.pairs J,
         N.Ψ p.1 p.2 (z p.1) (z p.2)) =
      ∏ p : PairEdge J,
        ∑ θ ∈ allowedLabels N p,
          N.f p.val.1 p.val.2 (z p.val.1) θ *
          N.f p.val.2 p.val.1 (z p.val.2) θ := by
    rw [← Finset.prod_attach (Groundwork.pairs J)]
    apply Finset.prod_congr rfl
    intro p _
    exact source_pair_expansion N z p
  rw [hp]
  rw [Finset.prod_univ_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  rfl

#print axioms IndependentETH.SourceIncidence.value_eq_incidence

end IndependentETH.SourceIncidence
