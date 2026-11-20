import Mathlib

/-!
# Exact staged contraction for overlapping factor scopes

A factor may depend on several shared Boolean variables. We express its
declared scope as a finite set of variable names and require a locality
certificate: changing a variable outside that scope does not change the
factor's value.

The theorem covers any number of such factors, arbitrary overlapping
declared scopes, arbitrary processing order, and arbitrary commutative
semiring weights. Each elimination list must be safe for every *future*
factor. No small-width or runtime claim is made.

The native Rust GF(2) representation is NOT refined by this proof.
-/

namespace IndependentETH.OverlappingFactors

open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

abbrev Assignment (V : Type*) := V → Bool
abbrev Weight (V R : Type*) := Assignment V → R

/-- Pointwise multiplication of functions on the same global assignment. -/
def times (f g : Weight V R) : Weight V R :=
  fun x => f x * g x

theorem times_assoc (f g h : Weight V R) :
    times (times f g) h = times f (times g h) := by
  funext x
  exact mul_assoc (f x) (g x) (h x)

/-- Sum over the two values of one Boolean variable, retaining all others. -/
def eliminateAt (v : V) (f : Weight V R) : Weight V R :=
  fun x => f (Function.update x v false) +
    f (Function.update x v true)

/-- Eliminate a list of Boolean variables, in the explicit given order. -/
def eliminateList (xs : List V) (f : Weight V R) : Weight V R :=
  xs.foldl (fun acc v => eliminateAt v acc) f

theorem eliminateList_append (xs ys : List V) (f : Weight V R) :
    eliminateList (xs ++ ys) f =
      eliminateList ys (eliminateList xs f) := by
  simp only [eliminateList, List.foldl_append]

/-- Pull a factor past one exact sum only when it ignores the summed bit. -/
theorem eliminateAt_mul_of_invariant
    (v : V) (f g : Weight V R)
    (h : ∀ x b, g (Function.update x v b) = g x) :
    times (eliminateAt v f) g =
      eliminateAt v (times f g) := by
  funext x
  change
    (f (Function.update x v false) +
      f (Function.update x v true)) * g x =
    f (Function.update x v false) *
      g (Function.update x v false) +
    f (Function.update x v true) *
      g (Function.update x v true)
  rw [h x false, h x true, add_mul]

/-- Pull a future factor past an arbitrary sequence of previously
eliminated variables, provided it ignores every one of them. -/
theorem eliminateList_mul_of_invariant
    (xs : List V) (f g : Weight V R)
    (h : ∀ v ∈ xs, ∀ x b, g (Function.update x v b) = g x) :
    times (eliminateList xs f) g =
      eliminateList xs (times f g) := by
  induction xs generalizing f with
  | nil => rfl
  | cons v vs ih =>
      have hv : ∀ x b, g (Function.update x v b) = g x := by
        intro x b
        exact h v (by simp) x b
      have hvs : ∀ w ∈ vs, ∀ x b,
          g (Function.update x w b) = g x := by
        intro w hw x b
        exact h w (by simp [hw]) x b
      change
        times (eliminateList vs (eliminateAt v f)) g =
        eliminateList vs (eliminateAt v (times f g))
      rw [ih (eliminateAt v f) hvs]
      rw [eliminateAt_mul_of_invariant v f g hv]

/-- A scope certificate: every variable omitted from the declared scope
is semantically irrelevant to the factor, for every full assignment. -/
structure ScopedFactor (V R : Type*) [DecidableEq V] where
  scope : Finset V
  value : Weight V R
  local_update : ∀ v, v ∉ scope →
    ∀ x b, value (Function.update x v b) = value x

/-- One factor and exactly the variables newly eliminated after accepting it.
A legal plan must not use those variables in later factors. -/
structure Step (V R : Type*) [DecidableEq V] where
  factor : ScopedFactor V R
  dead : List V

def eliminated : List (Step V R) → List V
  | [] => []
  | s :: rest => s.dead ++ eliminated rest

/-- Product of arbitrary overlapping-scope factors. Shared variables
are *one global variable*, not cloned per factor. -/
def factorProduct : List (Step V R) → Weight V R
  | [] => fun _ => 1
  | s :: rest => times s.factor.value (factorProduct rest)

/-- Staged execution of the abstract exact operator. This definition
is specification-level and does not implement Rust Gaussian elimination. -/
def contract (acc : Weight V R) : List (Step V R) → Weight V R
  | [] => acc
  | s :: rest =>
      contract (eliminateList s.dead (times acc s.factor.value)) rest

/-- Semantic safety: no future factor may depend on any variable that
the earlier stages have already eliminated. -/
def Safe (hidden : List V) : List (Step V R) → Prop
  | [] => True
  | s :: rest =>
      (∀ v ∈ hidden, v ∉ s.factor.scope) ∧
      Safe (hidden ++ s.dead) rest

/-- Union of the declared supports of the factors still unprocessed. -/
def scopeUnion : List (ScopedFactor V R) → Finset V
  | [] => ∅
  | f :: rest => f.scope ∪ scopeUnion rest

/-- Actual liveness construction: keep exactly ports needed by the
remaining source scopes or by the requested external output. -/
def nextKept (active : Finset V) (f : ScopedFactor V R)
    (rest : List (ScopedFactor V R)) (output : Finset V) :
    Finset V :=
  (active ∪ f.scope) ∩ (scopeUnion rest ∪ output)

/-- Newly dead ports, deterministically converted to an elimination list. -/
def nextDead (active : Finset V) (f : ScopedFactor V R)
    (rest : List (ScopedFactor V R)) (output : Finset V) :
    List V :=
  ((active ∪ f.scope) \ (scopeUnion rest ∪ output)).toList

/-- A complete order-respecting plan. Source factors may share ports
with preceding and following factors; only actual future dependencies
prevent elimination. -/
def makePlan (active output : Finset V) :
    List (ScopedFactor V R) → List (Step V R)
  | [] => []
  | f :: rest =>
      { factor := f, dead := nextDead active f rest output } ::
      makePlan (nextKept active f rest output) output rest

/-- The set-based liveness constructor implies the semantic safety
premise required for exact contraction: no already hidden variable
ever appears in a future declared factor scope. -/
theorem makePlan_safe
    (active output : Finset V) (factors : List (ScopedFactor V R)) :
    ∀ (hidden : List V),
      (∀ v ∈ hidden, v ∉ scopeUnion factors) →
      Safe hidden (makePlan active output factors) := by
  induction factors generalizing active with
  | nil =>
      intro hidden _
      trivial
  | cons f rest ih =>
      intro hidden hhidden
      change (∀ v ∈ hidden, v ∉ f.scope) ∧
        Safe (hidden ++ nextDead active f rest output)
          (makePlan (nextKept active f rest output) output rest)
      constructor
      · intro v hv
        have hh := hhidden v hv
        simp only [scopeUnion, Finset.mem_union, not_or] at hh
        exact hh.1
      · apply ih
        intro v hv
        rcases List.mem_append.mp hv with hold | hnew
        · have hh := hhidden v hold
          simp only [scopeUnion, Finset.mem_union, not_or] at hh
          exact hh.2
        · have hh : v ∈ (active ∪ f.scope) \
              (scopeUnion rest ∪ output) := by
            simpa only [nextDead, Finset.mem_toList] using hnew
          have hnot : v ∉ scopeUnion rest ∪ output :=
            (Finset.mem_sdiff.mp hh).2
          simp only [Finset.mem_union, not_or] at hnot
          exact hnot.1

/-- General overlap theorem: arbitrary scopes may share any variables
that remain live. The recursive staged contraction equals the direct
product of ALL factors followed by exactly the recorded eliminations.

The theorem is symbolic and uniform in the initial accumulator, all
assignments, the number/order of factors, and the coefficient semiring.
An external plan must additionally ensure each dead variable is summed
once and that every variable intended to be hidden is eventually removed. -/
theorem contract_correct (steps : List (Step V R)) :
    ∀ (hidden : List V) (base : Weight V R),
      Safe hidden steps →
      contract (eliminateList hidden base) steps =
        eliminateList (hidden ++ eliminated steps)
          (times base (factorProduct steps)) := by
  induction steps with
  | nil =>
      intro hidden base _
      change eliminateList hidden base =
        eliminateList (hidden ++ [])
          (times base (fun _ => 1))
      simp only [List.append_nil]
      congr 1
      funext x
      simp only [times, mul_one]
  | cons s rest ih =>
      intro hidden base hsafe
      obtain ⟨hscope, hrest⟩ := hsafe
      have hlocal : ∀ v ∈ hidden, ∀ x b,
          s.factor.value (Function.update x v b) =
          s.factor.value x := by
        intro v hv x b
        exact s.factor.local_update v (hscope v hv) x b
      calc
        contract (eliminateList hidden base) (s :: rest) =
            contract
              (eliminateList s.dead
                (times (eliminateList hidden base) s.factor.value))
              rest := rfl
        _ = contract
              (eliminateList (hidden ++ s.dead)
                (times base s.factor.value)) rest := by
              rw [eliminateList_mul_of_invariant hidden base s.factor.value hlocal]
              rw [eliminateList_append]
        _ = eliminateList ((hidden ++ s.dead) ++ eliminated rest)
              (times (times base s.factor.value)
                (factorProduct rest)) :=
              ih (hidden ++ s.dead) (times base s.factor.value) hrest
        _ = eliminateList (hidden ++ eliminated (s :: rest))
              (times base (factorProduct (s :: rest))) := by
              simp only [eliminated, factorProduct,
                List.append_assoc, times_assoc]

/-- An ordinary uncompressed starting function satisfies the same result,
with no initially eliminated variables. -/
theorem contract_from_raw
    (steps : List (Step V R)) (base : Weight V R)
    (hsafe : Safe [] steps) :
    contract base steps =
      eliminateList (eliminated steps)
        (times base (factorProduct steps)) := by
  simpa [eliminateList] using
    (contract_correct steps [] base hsafe)

#print axioms IndependentETH.OverlappingFactors.eliminateAt_mul_of_invariant
#print axioms IndependentETH.OverlappingFactors.eliminateList_mul_of_invariant
#print axioms IndependentETH.OverlappingFactors.contract_correct
#print axioms IndependentETH.OverlappingFactors.contract_from_raw

/-- The Rust-style future-scope planner automatically meets the safety
precondition of the general overlapping-factor contraction theorem. -/
theorem generated_plan_correct
    (active output : Finset V)
    (factors : List (ScopedFactor V R)) (base : Weight V R) :
    contract base (makePlan active output factors) =
      eliminateList (eliminated (makePlan active output factors))
        (times base (factorProduct (makePlan active output factors))) := by
  apply contract_from_raw
  apply makePlan_safe
  intro v hv
  cases hv

#print axioms IndependentETH.OverlappingFactors.makePlan_safe
#print axioms IndependentETH.OverlappingFactors.generated_plan_correct

