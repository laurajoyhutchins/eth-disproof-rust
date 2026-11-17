import Mathlib
import ACC.Circuit
import Groundwork.Net.Net
import OAI.Algorithms.SubexponentialSAT.SAT

/-!
# Source-defined counting factors lowered into the same arithmetic circuit IR

This adapter uses the pinned, unchanged Anthropic Groundwork Network and OpenAI
SAT definitions. Each atom is ONE source factor: no atomic gate computes an
entire network contraction or a #SAT answer.

The generated syntax is an explicit exhaustive tree. Its correctness is a
semantic foundation, not an efficient execution path. No OpenAI packet/mode
implementation is claimed here.
-/

namespace ACC.Source

open scoped BigOperators

/-! ## Anthropic's original finite network -/

inductive NetworkAtom (J σ τ : Type*) where
  | node : J → σ → NetworkAtom J σ τ
  | edge : J → J → σ → τ → NetworkAtom J σ τ

def networkAtomValue {J σ τ : Type*}
    (N : Groundwork.Network J σ τ) : NetworkAtom J σ τ → ℤ
  | .node a s => N.W a s
  | .edge a b s label => N.f a b s label

/--
A factor-explicit circuit for the ACTUAL Anthropic Network.value definition.
The source's allowed node states and edge labels determine the finite sums.
-/
noncomputable def networkCircuit {J σ τ : Type*}
    [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) : Circuit (NetworkAtom J σ τ) := by
  classical
  exact Circuit.sumFinset (Fintype.piFinset N.S) (fun z =>
    .mul
      (Circuit.prodFinset (Finset.univ : Finset J) (fun a =>
        .atom (.node a (z a))))
      (Circuit.prodFinset (Groundwork.pairs J) (fun pair =>
        Circuit.sumFinset (N.Θ (min pair.1 pair.2) (max pair.1 pair.2))
          (fun label =>
            .mul (.atom (.edge pair.1 pair.2 (z pair.1) label))
                 (.atom (.edge pair.2 pair.1 (z pair.2) label))))))

/-- The arithmetic circuit evaluates to the ORIGINAL pinned network value. -/
theorem networkCircuit_correct {J σ τ : Type*}
    [Fintype J] [LinearOrder J]
    (N : Groundwork.Network J σ τ) :
    (networkCircuit N).eval (networkAtomValue N) = N.value := by
  classical
  change (networkCircuit N).eval (networkAtomValue N) =
    ∑ z ∈ Fintype.piFinset N.S,
      (∏ a, N.W a (z a)) *
        ∏ pair ∈ Groundwork.pairs J,
          ∑ label ∈ N.Θ (min pair.1 pair.2) (max pair.1 pair.2),
            N.f pair.1 pair.2 (z pair.1) label *
              N.f pair.2 pair.1 (z pair.2) label
  simp [networkCircuit, networkAtomValue,
    Circuit.eval_sumFinset, Circuit.eval_prodFinset, Circuit.eval]

/--
Anthropic's exact source merge is a certified, value-preserving rewrite
between two potentially different typed factor circuits.
This says nothing about their construction costs or compressed-state closure.
-/
theorem network_merge_circuit_correct
    {J J' σ τ : Type*}
    [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Groundwork.Network J σ τ) (color : J → J')
    (outsideState : σ) (outsideLabel : τ) :
    (networkCircuit (N.merge color outsideState outsideLabel)).eval
      (networkAtomValue (N.merge color outsideState outsideLabel)) =
    (networkCircuit N).eval (networkAtomValue N) := by
  rw [networkCircuit_correct, networkCircuit_correct]
  exact Groundwork.Network.value_merge N color outsideState outsideLabel

/-! ## OpenAI's original finite CNF semantics (not its packet algorithm) -/

open OAI.Algorithms.SubexponentialSAT

inductive SATAtom (n : ℕ) where
  | clause : (Fin n → Bool) → SAT.Clause (Fin n) → SATAtom n

def satAtomValue {n : ℕ} : SATAtom n → ℤ
  | .clause a C => if C.eval a = true then 1 else 0

/--
This circuit has one clause factor for each clause/assignment pair.
The complete formula's truth value is NOT an atomic oracle.
-/
noncomputable def satCircuit {n : ℕ}
    (F : SAT.CNF (Fin n)) : Circuit (SATAtom n) := by
  classical
  exact Circuit.sumFinset (Finset.univ : Finset (Fin n → Bool)) (fun a =>
    Circuit.prodFinset F (fun C => .atom (.clause a C)))

private theorem clause_product_is_indicator {n : ℕ}
    (F : SAT.CNF (Fin n)) (a : Fin n → Bool) :
    (∏ C ∈ F, satAtomValue (SATAtom.clause a C)) =
      if F.eval a = true then (1 : ℤ) else 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp [satAtomValue]
  | @insert C F hn ih =>
      rw [Finset.prod_insert hn, SAT.CNF.eval_insert]
      cases hc : C.eval a <;> cases hf : F.eval a <;>
        simp [satAtomValue, hc, hf, ih]

private theorem indicator_sum_eq_card {α : Type*} [DecidableEq α]
    (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ a ∈ s, if P a then (1 : ℤ) else 0) = (s.filter P).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hp : P a <;> simp [hp, ha, ih]

/-- Source-semantic correctness, including unused declared variables. -/
theorem satCircuit_correct {n : ℕ} (F : SAT.CNF (Fin n)) :
    (satCircuit F).eval satAtomValue = (SAT.count F : ℤ) := by
  classical
  calc
    (satCircuit F).eval satAtomValue =
        ∑ a ∈ (Finset.univ : Finset (Fin n → Bool)),
          ∏ C ∈ F, satAtomValue (SATAtom.clause a C) := by
      simp [satCircuit, Circuit.eval_sumFinset, Circuit.eval_prodFinset,
        Circuit.eval]
    _ = ∑ a ∈ (Finset.univ : Finset (Fin n → Bool)),
          if F.eval a = true then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      exact clause_product_is_indicator F a
    _ = (SAT.count F : ℤ) := by
      simpa [SAT.count, SAT.satisfyingAssignments] using
        (indicator_sum_eq_card
          (Finset.univ : Finset (Fin n → Bool))
          (fun a => F.eval a = true))

#print axioms ACC.Source.networkCircuit_correct
#print axioms ACC.Source.network_merge_circuit_correct
#print axioms ACC.Source.satCircuit_correct

end ACC.Source
