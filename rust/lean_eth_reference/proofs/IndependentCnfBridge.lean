import Mathlib
import OAI.Algorithms.SubexponentialSAT.SAT
import MainResults

/-!
# Independent CNF semantics bridge

OpenAI source: openai/math@4eaee87548250b2682affda7d05d947c05554bae
  lean/OAI/Algorithms/SubexponentialSAT/SAT.lean
Anthropic source: anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5
  eth/MainResults.lean

These imports are the **original pinned declarations**, supplied by the
independent-formulations CI workflow. This file translates only the finite
formula representation and proves a universally quantified count identity.

It neither compares the two Turing machines nor proves their running time.
-/

namespace IndependentETH

open OAI.Algorithms.SubexponentialSAT

/-- Anthropic's `(Fin n × Bool)` literal as OpenAI's indexed literal. -/
def toLiteral {n : ℕ} (l : MainResults.Lit n) : SAT.Literal (Fin n) :=
  ⟨l.1, l.2⟩

/-- Forget order and repeated literals in a clause; OR is unchanged. -/
def toClause {n : ℕ} (C : List (MainResults.Lit n)) : SAT.Clause (Fin n) :=
  (C.map toLiteral).toFinset

/-- Forget order and repeated clauses; AND is unchanged. -/
def toCNF {n : ℕ} (φ : MainResults.CNF n) : SAT.CNF (Fin n) :=
  (φ.map toClause).toFinset

theorem clause_eval_iff {n : ℕ} (a : Fin n → Bool) (C : List (MainResults.Lit n)) :
    (toClause C).eval a = true ↔ ∃ l ∈ C, a l.1 = l.2 := by
  rw [SAT.Clause.eval_eq_true]
  simp only [toClause, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l', ⟨l, hl, rfl⟩, he⟩
    refine ⟨l, hl, ?_⟩
    simpa [toLiteral] using (SAT.Literal.eval_eq_true a (toLiteral l)).mp he
  · rintro ⟨l, hl, he⟩
    refine ⟨toLiteral l, ⟨l, hl, rfl⟩, ?_⟩
    apply (SAT.Literal.eval_eq_true a (toLiteral l)).mpr
    simpa [toLiteral] using he

theorem cnf_eval_iff {n : ℕ} (a : Fin n → Bool) (φ : MainResults.CNF n) :
    (toCNF φ).eval a = true ↔
      ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2 := by
  rw [SAT.CNF.eval_eq_true]
  simp only [toCNF, List.mem_toFinset, List.mem_map]
  constructor
  · intro h C hC
    exact (clause_eval_iff a C).mp (h (toClause C) ⟨C, hC, rfl⟩)
  · intro h C' hC'
    obtain ⟨C, hC, rfl⟩ := hC'
    exact (clause_eval_iff a C).mpr (h C hC)

/-- Unconditional equivalence of the two definitions of SAT. -/
theorem satisfiable_iff {n : ℕ} (φ : MainResults.CNF n) :
    MainResults.Satisfiable φ ↔ SAT.Satisfiable (toCNF φ) := by
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a, (cnf_eval_iff a φ).mpr h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, (cnf_eval_iff a φ).mp h⟩

/-- Exact #SAT equality for every list-of-lists CNF, with no eligibility
hypotheses. The number of variables n remains fixed even if variables are
unused. This theorem is independent of either machine's complexity claim. -/
theorem numSat_eq_count {n : ℕ} (φ : MainResults.CNF n) :
    MainResults.numSat φ = SAT.count (toCNF φ) := by
  unfold MainResults.numSat SAT.count SAT.satisfyingAssignments
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (cnf_eval_iff a φ).symm

#print axioms IndependentETH.satisfiable_iff
#print axioms IndependentETH.numSat_eq_count

end IndependentETH
