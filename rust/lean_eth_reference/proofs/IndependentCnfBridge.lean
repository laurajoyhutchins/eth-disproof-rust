import Mathlib
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.IndependentAnthropic.MainResults

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

/-
## Common-domain and complete Anthropic machine theorem transfer

This is a consequence of the exact original Anthropic MainTheorem *statement*
together with the already kernel-checked equivalence between its CNF lists
and the OpenAI SAT finite-set representation. Unlike an output-only test, it
retains one uniform original TM2 machine, its input encoding, and every
quantified time bound from MainTheorem.

The parameter hMain is the external published Anthropic proof
MainResults.mainTheorem : MainResults.MainTheorem. This module imports the
original *statement*, not its enormous proof dependencies. Accordingly
the theorem is a proved implication, not a new unconditional proof of ETH.

The original OpenAI primitive-machine runtime theorem is a separate
source endpoint, SqrtLogSpace.exact_count_and_sat. This module does not
import it and claims neither identical machines nor equal time bounds.
-/

/-
The converse translation picks a deterministic finite-set list
representation. It preserves distinct clauses: the input OpenAI
Finset contains each clause at most once, and fromClause is injective
because converting the result back returns that exact original clause.
-/

/-- Original OpenAI literal as an Anthropic pair of index and polarity. -/
def fromLiteral {n : ℕ}
    (l : SAT.Literal (Fin n)) : MainResults.Lit n :=
  ⟨l.variable, l.positive⟩

@[simp] theorem toLiteral_fromLiteral {n : ℕ}
    (l : SAT.Literal (Fin n)) : toLiteral (fromLiteral l) = l := by
  cases l
  rfl

/-- Every OpenAI finite-set clause admits a unique chosen list encoding. -/
def fromClause {n : ℕ}
    (C : SAT.Clause (Fin n)) : List (MainResults.Lit n) :=
  C.toList.map fromLiteral

@[simp] theorem toClause_fromClause {n : ℕ}
    (C : SAT.Clause (Fin n)) : toClause (fromClause C) = C := by
  classical
  simp [toClause, fromClause, List.map_map, Function.comp_def]

/-- The source finite-set formula gives an Anthropic list-of-lists CNF. -/
def fromCNF {n : ℕ}
    (F : SAT.CNF (Fin n)) : MainResults.CNF n :=
  F.toList.map fromClause

/-- The CNF translation is surjective, with an explicit right inverse. -/
@[simp] theorem toCNF_fromCNF {n : ℕ}
    (F : SAT.CNF (Fin n)) : toCNF (fromCNF F) = F := by
  classical
  simp [toCNF, fromCNF, List.map_map, Function.comp_def]

/--
OpenAI's finite-set width property implies Anthropic's original
IsKCNF, including its requirement that no clause *list* repeats.
-/
theorem fromCNF_IsKCNF
    {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    MainResults.IsKCNF k (fromCNF F) := by
  classical
  constructor
  · intro C hC
    simp only [fromCNF, List.mem_map, Finset.mem_toList] at hC
    obtain ⟨C₀, hmem, rfl⟩ := hC
    simpa [fromClause] using hw C₀ hmem
  · have hInjective : Function.Injective
        (fromClause : SAT.Clause (Fin n) → List (MainResults.Lit n)) := by
      intro C D h
      have hh := congrArg toClause h
      simpa using hh
    exact (Finset.nodup_toList F).map hInjective

/-- Every OpenAI formula keeps exactly the same #SAT after the round trip. -/
theorem fromCNF_count_eq {n : ℕ}
    (F : SAT.CNF (Fin n)) :
    MainResults.numSat (fromCNF F) = SAT.count F := by
  rw [numSat_eq_count, toCNF_fromCNF]

/-- Anthropic's k-CNF eligibility implies OpenAI's width hypothesis. -/
theorem toCNF_width_at_most
    {n k : ℕ} (φ : MainResults.CNF n)
    (hK : MainResults.IsKCNF k φ) :
    SAT.WidthAtMost k (toCNF φ) := by
  intro C hC
  simp only [toCNF, List.mem_toFinset, List.mem_map] at hC
  obtain ⟨C₀, hmem, rfl⟩ := hC
  calc
    (toClause C₀).card = (C₀.map toLiteral).toFinset.card := rfl
    _ ≤ (C₀.map toLiteral).length := List.toFinset_card_le _
    _ = C₀.length := by simp
    _ ≤ k := hK.1 C₀ hmem

/--
**Quantitative machine-level bridge in Anthropic's exact native model.**

Assuming the original source theorem MainTheorem, one *single*
finite-alphabet Anthropic TM2 machine and one source-defined constant C
work uniformly for all k,n,φ satisfying the original eligibility
hypotheses. The output word denotes the actual OpenAI SAT.count of the
translated formula, and the original precise timeMin bound is retained.

This does NOT silently replace Anthropic's input word by OpenAI's
encodeCNF: the machine still reads exactly Anthropic.encInput k φ.
-/
theorem original_anthropic_machine_counts_openai_with_rate
    (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k n : ℕ) (φ : MainResults.CNF n),
        1 ≤ k → MainResults.IsKCNF k φ →
        2 ≤ φ.length → 4 ≤ n → MainResults.AllOccur φ →
        SAT.WidthAtMost k (toCNF φ) ∧
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((MainResults.encInput k φ).map M.inputAlphabet.invFun)
          (some ((MainResults.binary n (SAT.count (toCNF φ))).map
            M.outputAlphabet.invFun))
          (MainResults.timeMin C k φ.length n)) := by
  obtain ⟨M, C, hfinite, hrun⟩ := hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro k n φ hk hK hm hn hoc
  refine ⟨toCNF_width_at_most φ hK, ?_⟩
  have hr : MainResults.CountsWithin M k φ
      (MainResults.timeMin C k φ.length n) :=
    hrun k n φ hk hK hm hn hoc
  dsimp [MainResults.CountsWithin] at hr
  simpa only [Equiv.invFun_as_coe, numSat_eq_count] using hr

#print axioms IndependentETH.satisfiable_iff
#print axioms IndependentETH.numSat_eq_count
#print axioms IndependentETH.toCNF_width_at_most
#print axioms IndependentETH.original_anthropic_machine_counts_openai_with_rate
/--
The reverse quantitative transport, for an ORIGINAL OpenAI Finset CNF.
The original Anthropic machine runs on an Anthropic list encoding
*constructed from that very Finset*, and its original bound uses the
number of distinct OpenAI clauses, F.card. Its result is SAT.count F.

The original eligibility requirement AllOccur remains explicit.
No computation-time claim for preparing the input word from another
machine's input encoding is smuggled into this theorem.
-/
theorem original_anthropic_machine_counts_any_eligible_openai_cnf
    (hMain : MainResults.MainTheorem) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℕ),
      (∀ i, Finite (M.tm.Γ i)) ∧
      ∀ (k n : ℕ) (F : SAT.CNF (Fin n)),
        2 ≤ k → SAT.WidthAtMost k F →
        2 ≤ F.card → 4 ≤ n →
        MainResults.AllOccur (fromCNF F) →
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((MainResults.encInput k (fromCNF F)).map
            M.inputAlphabet.invFun)
          (some ((MainResults.binary n (SAT.count F)).map
            M.outputAlphabet.invFun))
          (MainResults.timeMin C k F.card n)) := by
  obtain ⟨M, C, hfinite, hrun⟩ :=
    original_anthropic_machine_counts_openai_with_rate hMain
  refine ⟨M, C, hfinite, ?_⟩
  intro k n F hk hwidth hm hn hoc
  have hlength : (fromCNF F).length = F.card := by
    simp [fromCNF]
  have hK := fromCNF_IsKCNF F hwidth
  have hrun' := (hrun k n (fromCNF F)
      (by omega) hK (by simpa [hlength] using hm) hn hoc).2
  simpa only [toCNF_fromCNF, hlength] using hrun'

#print axioms IndependentETH.toCNF_fromCNF
#print axioms IndependentETH.fromCNF_IsKCNF
#print axioms IndependentETH.fromCNF_count_eq
#print axioms IndependentETH.original_anthropic_machine_counts_any_eligible_openai_cnf


end IndependentETH
