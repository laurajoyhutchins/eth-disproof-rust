import Mathlib

/-!
# Unit-resolution implication and two-way source refutation

These elementary lemmas justify a checked certificate boundary for
source-derived early pruning of the FINAL #SAT objective. They do not
identify the actual Rust trace checker with Lean, nor do they permit
replacing an intermediate processed-prefix count with a pruned count
when that prefix is observed independently.
-/

namespace IndependentETH.UnitRefutation

abbrev Literal := String × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause
abbrev Partial := String → Option Bool

def extendsPartial (a : String → Bool) (p : Partial) : Prop :=
  ∀ v value, p v = some value → a v = value

def clauseTrue (a : String → Bool) (clause : Clause) : Prop :=
  ∃ lit ∈ clause, a lit.1 = lit.2

def cnfTrue (a : String → Bool) (cnf : CNF) : Prop :=
  ∀ clause ∈ cnf, clauseTrue a clause

def allFalse (p : Partial) (clause : Clause) : Prop :=
  ∀ lit ∈ clause, p lit.1 = some (!lit.2)

/-- An exact clause-only contradiction under a fixed boundary partial
assignment cannot be satisfied by any total completion. -/
theorem empty_reason_sound
    (a : String → Bool) (p : Partial) (clause : Clause)
    (hext : extendsPartial a p) (hfalse : allFalse p clause) :
    ¬ clauseTrue a clause := by
  rintro ⟨lit, hmem, htrue⟩
  have hf := hext lit.1 (!lit.2) (hfalse lit hmem)
  cases lit.2 <;> simp_all

def unitReason (p : Partial) (clause : Clause)
    (v : String) (sign : Bool) : Prop :=
  (v, sign) ∈ clause ∧ p v = none ∧
    ∀ lit ∈ clause, lit ≠ (v, sign) →
      p lit.1 = some (!lit.2)

/-- If a source clause is unit under a partial assignment, every
satisfying extension must have the forced value. This is the sound
primitive used in independently replaying a sequence of reasons. -/
theorem unit_reason_forces
    (a : String → Bool) (p : Partial) (clause : Clause)
    (v : String) (sign : Bool)
    (hext : extendsPartial a p)
    (hsat : clauseTrue a clause)
    (hunit : unitReason p clause v sign) :
    a v = sign := by
  rcases hsat with ⟨lit, hmem, htrue⟩
  rcases hunit with ⟨_, _, hothers⟩
  by_cases h : lit = (v, sign)
  · simpa [h] using htrue
  · have hf := hext lit.1 (!lit.2) (hothers lit hmem h)
    cases lit.2 <;> simp_all

/-- An exhaustive one-v split is a valid refutation when both
branches are incompatible with the source CNF and the same boundary
assumptions. The Rust checker additionally checks each branch's
source-indexed unit trace; that implementation refinement remains open. -/
theorem two_branches_refute
    (cnf : CNF) (p : Partial) (v : String)
    (hfalse : ∀ a, extendsPartial a p →
      a v = false → ¬ cnfTrue a cnf)
    (htrue : ∀ a, extendsPartial a p →
      a v = true → ¬ cnfTrue a cnf) :
    ∀ a, extendsPartial a p → ¬ cnfTrue a cnf := by
  intro a hext
  cases hv : a v with
  | false => exact hfalse a hext hv
  | true => exact htrue a hext hv

/-- The final-count pruning criterion: once the future source CNF is
refuted for a retained boundary assignment, no satisfying total
assignment extending that boundary can contribute to #SAT. -/
theorem future_refutation_eliminates
    (future : CNF) (p : Partial)
    (hrefute : ∀ a, extendsPartial a p → ¬ cnfTrue a future) :
    ¬ ∃ a, extendsPartial a p ∧ cnfTrue a future := by
  rintro ⟨a, ha, hs⟩
  exact hrefute a ha hs

/-- Reusable nogoods are monotone under *extension* of the assumptions
used for a checked contradiction. A cached proof may have been replayed
under fewer assumptions than the original source boundary assignment.
It remains valid under every assignment extending those assumptions. -/
theorem cached_refutation_monotone
    (future : CNF) (weak strong : Partial)
    (hsub : ∀ name value, weak name = some value →
      strong name = some value)
    (hrefute : ∀ a, extendsPartial a weak → ¬ cnfTrue a future) :
    ∀ a, extendsPartial a strong → ¬ cnfTrue a future := by
  intro a hext
  apply hrefute a
  intro name value hw
  exact hext name value (hsub name value hw)

/-- The final natural #SAT sum is unchanged by dropping a processed
prefix's boundary contribution only when its *future* count is certified
zero. The pruned prefix alone is NOT generally equal to the original. -/
theorem contextual_zero_count_preserved {α : Type} (s : Finset α)
    (prefixCount future : α → ℕ) (cachedMatch : α → Prop)
    [DecidablePred cachedMatch]
    (hsound : ∀ i ∈ s, cachedMatch i → future i = 0) :
    (∑ i ∈ s, prefixCount i * future i) =
      ∑ i ∈ s, if cachedMatch i then 0 else prefixCount i * future i := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : cachedMatch i
  · simp [hc, hsound i hi hc]
  · simp [hc]

/-- Removing all literals of a pivot variable from a source clause.
The Rust resolution checker additionally requires a complementary pivot
and checks its original-source lineage. -/
def withoutVar (clause : Clause) (pivot : String) : Clause :=
  clause.filter (fun lit => lit.1 != pivot)

def sourceResolvent (left right : Clause) (pivot : String) : Clause :=
  withoutVar left pivot ++ withoutVar right pivot

/-- One source resolution step preserves truth: if all occurrences of the
pivot in the left clause are positive and all on the right are negative,
then any assignment satisfying both parents satisfies the resolvent.
No cost or bounded-representation claim follows from resolution soundness. -/
theorem source_resolution_sound
    (a : String → Bool) (left right : Clause) (pivot : String)
    (hleft : ∀ lit ∈ left, lit.1 = pivot → lit.2 = true)
    (hright : ∀ lit ∈ right, lit.1 = pivot → lit.2 = false)
    (hl : clauseTrue a left) (hr : clauseTrue a right) :
    clauseTrue a (sourceResolvent left right pivot) := by
  cases hv : a pivot with
  | false =>
      rcases hl with ⟨lit, hmem, htrue⟩
      have haway : lit.1 ≠ pivot := by
        intro heq
        have hp := hleft lit hmem heq
        have contra : a pivot = true := by simpa [heq, hp] using htrue
        rw [hv] at contra
        cases contra
      refine ⟨lit, ?_, htrue⟩
      simp [sourceResolvent, withoutVar, haway, hmem]
  | true =>
      rcases hr with ⟨lit, hmem, htrue⟩
      have haway : lit.1 ≠ pivot := by
        intro heq
        have hp := hright lit hmem heq
        have contra : a pivot = false := by simpa [heq, hp] using htrue
        rw [hv] at contra
        cases contra
      refine ⟨lit, ?_, htrue⟩
      simp [sourceResolvent, withoutVar, haway, hmem]

/-- A source rule determined solely by the retained output key
commutes with summing the contributions of all compatible support
pairs in that fiber. In particular, dropping individually forbidden
products before addition has the same final count as dropping their
aggregate output coefficient after addition.

This does not show that the Rust \`project\` or \`embed\` functions
compute the claimed fiber. The experimental Rust correspondence is
checked separately against name-based source enumeration. -/
theorem source_preproduct_pruning_commutes_with_fiber_sum
    {α β : Type} (pairs : Finset α) (outputOf : α → β)
    (output : β) (forbidden : β → Prop)
    [DecidablePred forbidden] (weight : α → ℕ)
    (hprojection : ∀ p ∈ pairs, outputOf p = output) :
    (∑ p ∈ pairs, if forbidden (outputOf p) then 0 else weight p)
      = (if forbidden output then 0 else ∑ p ∈ pairs, weight p) := by
  have hsum :
      (∑ p ∈ pairs, if forbidden (outputOf p) then 0 else weight p) =
        ∑ p ∈ pairs, if forbidden output then 0 else weight p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hprojection p hp]
  rw [hsum]
  by_cases h : forbidden output
  · simp [h]
  · simp [h]

/-- A memoized source-guard decision is correct only if every stored
answer agrees with the predicate computed from the *same checked*
source clause set, variable order, and retained boundary.

An absent entry falls back to the original source guard. The hypothesis
is a cache invariant; a separate executable check must establish that
Rust only inserts complete checked decisions and scopes the cache to
one frontier. An interrupted source scan is NOT a valid false entry. -/
theorem checked_frontier_memo_lookup_sound
    {β : Type} (sourceGuard : β → Bool)
    (memo : β → Option Bool)
    (hchecked : ∀ key result, memo key = some result →
      result = sourceGuard key)
    (key : β) :
    (memo key).getD (sourceGuard key) = sourceGuard key := by
  cases h : memo key with
  | none => simp [h]
  | some result =>
      simp [h, hchecked key result h]

/-- Repeated guard decisions cached under the exact same source
frontier cannot change the sum of surviving exact contributions.
This establishes logical memo equivalence, not that BTreeMap
keys or allocator contents satisfy the invariant in production. -/
theorem checked_frontier_memo_preserves_pair_sum
    {α β : Type} (pairs : Finset α)
    (outputOf : α → β) (weight : α → ℕ)
    (sourceGuard : β → Bool) (memo : β → Option Bool)
    (hchecked : ∀ key result, memo key = some result →
      result = sourceGuard key) :
    (∑ p ∈ pairs,
      if (memo (outputOf p)).getD (sourceGuard (outputOf p))
      then 0 else weight p) =
    ∑ p ∈ pairs, if sourceGuard (outputOf p) then 0 else weight p := by
  apply Finset.sum_congr rfl
  intro p _hp
  rw [checked_frontier_memo_lookup_sound sourceGuard memo hchecked (outputOf p)]

/-- A structurally selected cache may be enabled or bypassed without
changing the final exact natural-number sum, provided every stored
decision is source-guard faithful. This says nothing about whether
the *heuristic* cost estimate correctly predicts repeat rates. -/
theorem conditional_frontier_memo_preserves_pair_sum
    {α β : Type} (pairs : Finset α)
    (outputOf : α → β) (weight : α → ℕ)
    (sourceGuard : β → Bool) (memo : β → Option Bool)
    (enabled : Bool)
    (hchecked : ∀ key result, memo key = some result →
      result = sourceGuard key) :
    (∑ p ∈ pairs,
      if (if enabled
          then (memo (outputOf p)).getD (sourceGuard (outputOf p))
          else sourceGuard (outputOf p))
      then 0 else weight p) =
    ∑ p ∈ pairs, if sourceGuard (outputOf p) then 0 else weight p := by
  cases enabled with
  | false => simp
  | true =>
      simpa using checked_frontier_memo_preserves_pair_sum
        pairs outputOf weight sourceGuard memo hchecked

#print axioms empty_reason_sound
#print axioms unit_reason_forces
#print axioms two_branches_refute
#print axioms future_refutation_eliminates
#print axioms cached_refutation_monotone
#print axioms contextual_zero_count_preserved
#print axioms source_resolution_sound
#print axioms source_preproduct_pruning_commutes_with_fiber_sum
#print axioms checked_frontier_memo_lookup_sound
#print axioms checked_frontier_memo_preserves_pair_sum
#print axioms conditional_frontier_memo_preserves_pair_sum

end IndependentETH.UnitRefutation
