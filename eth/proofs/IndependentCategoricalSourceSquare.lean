import Mathlib
import IndependentCnfBridge
import IndependentAnthropicNetworkAdapter

/-!
# Source-backed parts of the ETH comparison squares

This module imports the existing, source-pinned and separately checked CNF
bridge and Anthropic network adapter. It proves their compatibility with
reduction modulo 2^p, including arbitrary p. The reduction square does not
identify Anthropic's crossing modes with OpenAI's two-adic packets.

The missing OpenAI appendix source-to-common-network adapter is intentionally
not an axiom or an argument to a theorem here. It remains an open obligation.
-/

namespace IndependentETH.Categorical

open OAI.Algorithms.SubexponentialSAT

/-- The original OpenAI and Anthropic CNF-count semantics agree mod 2^p. -/
theorem source_count_square_mod_two_power {n : ℕ}
    (φ : MainResults.CNF n) (p : ℕ) :
    (MainResults.numSat φ : ZMod (2 ^ p)) =
      (SAT.count (IndependentETH.toCNF φ) : ZMod (2 ^ p)) := by
  exact congrArg (fun k : ℕ => (k : ZMod (2 ^ p)))
    (IndependentETH.numSat_eq_count φ)

/-- Anthropic's actual source merge commutes with coefficient reduction. -/
theorem anthropic_merge_square_mod_two_power
    {J J' σ τ : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ) (color : J → J')
    (outsideState : σ) (outsideLabel : τ) (p : ℕ) :
    ((N.merge color outsideState outsideLabel).value : ZMod (2 ^ p)) =
      (N.value : ZMod (2 ^ p)) := by
  exact congrArg (fun z : ℤ => (z : ZMod (2 ^ p)))
    (Groundwork.Network.value_merge N color outsideState outsideLabel)

/-- This is the same source merge expressed in the common finite factor
contraction, followed by reduction modulo 2^p. -/
theorem anthropic_common_contraction_square_mod_two_power
    {J J' σ τ : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ) (color : J → J')
    (outsideState : σ) (outsideLabel : τ) (p : ℕ) :
    ((IndependentETH.SourceNetwork.contraction
      (N.merge color outsideState outsideLabel).S
      (N.merge color outsideState outsideLabel).W
      (N.merge color outsideState outsideLabel).Θ
      (N.merge color outsideState outsideLabel).f : ℤ) : ZMod (2 ^ p)) =
    ((IndependentETH.SourceNetwork.contraction N.S N.W N.Θ N.f : ℤ) :
      ZMod (2 ^ p)) := by
  exact congrArg (fun z : ℤ => (z : ZMod (2 ^ p)))
    (IndependentETH.SourceNetwork.anthropic_merge_preserves_contraction
      N color outsideState outsideLabel)

#print axioms IndependentETH.Categorical.source_count_square_mod_two_power
#print axioms IndependentETH.Categorical.anthropic_merge_square_mod_two_power
#print axioms IndependentETH.Categorical.anthropic_common_contraction_square_mod_two_power

end IndependentETH.Categorical
