import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramNative

/-!
# Original numerical readout: row and coefficient-slot obligations

No Lean.Meta importer, no replacement numerical algorithm, no flattened
physical graph. This file works directly with the pinned original OAI
StructuredCalls constructors and the previously compiled original module.

The source row/slot/loop identities are definitional. The execution theorems
use the actual source's Eval and UnaryForPrograms.Visits relations. A Visits
witness explicitly requires callback preservation of the unary counter:
without that premise, the stated visit and cost bound is NOT established.
-/

namespace OAI.Algorithms.SubexponentialSAT.ReadoutRow

open OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

/-- Original source-defined single coefficient operation: key, arithmetic
    accumulation through a lifted program, then unary index increment. -/
theorem slot_source :
    slot = .seq buildQuery (.seq wideAccumulate advanceU) := rfl

/-- The arithmetic call is the pinned source's real lifted accumulator.
    This theorem does not construct or execute the accumulator's code table. -/
theorem accumulate_source :
    wideAccumulate =
      .call (ProgramLinking.liftProgram accumulateProgram id widePorts) := rfl

/-- The source's register and stack embedding for the arithmetic call. -/
theorem wide_ports_source :
    widePorts = (Fin.castAdd 13 : Fin 27 → Fin 40) := rfl

/-- The source keeps the query cleanup and unary index advance in this order. -/
theorem advance_source :
    advanceU = .seq (wclear 16) (wpush 30 true) := rfl

/-- One numerical row is one zero-vector initialization, an inner source
    loop, and coefficient completion, with no change of association. -/
theorem row_source :
    row = .seq startRow (.seq inner finishRow) := rfl

/-- The source's actual seed and final transfer operations. -/
theorem start_row_source :
    startRow = .seq (wcopy 27 17 23) (wcopy 28 32 23) := rfl

theorem finish_row_source :
    finishRow = .seq (wtransfer 17 35) (.seq (wclear 30) (wpush 31 true)) := rfl

/-- The inner loop is source-defined as one initial pop, followed by a
    structured while guard with one slot callback and one pop per visit. -/
theorem inner_source :
    inner =
      .seq (UnaryForPrograms.popCmd innerPorts)
        (.while innerPorts.flag
          (.seq slot (UnaryForPrograms.popCmd innerPorts))) := rfl

/-- The mask loop runs before the rows, not inside every inner visit. -/
theorem mask_source :
    maskLoop =
      .seq (UnaryForPrograms.popCmd maskPorts)
        (.while maskPorts.flag
          (.seq (wpush 34 false) (UnaryForPrograms.popCmd maskPorts))) := rfl

/-- The original slot contributes exactly the source component sizes. -/
theorem slot_site_count :
    StructuredCalls.size slot =
      StructuredCalls.size buildQuery +
        (StructuredCalls.size wideAccumulate +
          StructuredCalls.size advanceU) := rfl

/-- Runtime U values do not unroll the inner control in the instruction table. -/
theorem inner_site_count :
    StructuredCalls.size inner = StructuredCalls.size slot + 3 := by
  change 1 + ((StructuredCalls.size slot + 1) + 1) =
    StructuredCalls.size slot + 3
  omega

theorem mask_site_count :
    StructuredCalls.size maskLoop = StructuredCalls.size (wpush 34 false) + 3 := by
  change 1 + ((StructuredCalls.size (wpush 34 false) + 1) + 1) =
    StructuredCalls.size (wpush 34 false) + 3
  omega

/-- The row keeps its static source size even for arbitrarily many U visits. -/
theorem row_site_count :
    StructuredCalls.size row =
      StructuredCalls.size startRow +
        (StructuredCalls.size slot + 3 + StructuredCalls.size finishRow) := by
  change StructuredCalls.size startRow +
      (StructuredCalls.size inner + StructuredCalls.size finishRow) = _
  rw [inner_site_count]

/-- Exact source-level factorization of one coefficient slot.
    Neither direction replaces the source's dictionary arithmetic. -/
theorem slot_eval_iff (n : ℕ) (a b : StructuredCalls.State 8 40) :
    StructuredCalls.Eval slot n a b ↔
      ∃ (nq na nu : ℕ) (queried summed : StructuredCalls.State 8 40),
        n = nq + (na + nu) ∧
        StructuredCalls.Eval buildQuery nq a queried ∧
        StructuredCalls.Eval wideAccumulate na queried summed ∧
        StructuredCalls.Eval advanceU nu summed b := by
  constructor
  · intro h
    change StructuredCalls.Eval
      (.seq buildQuery (.seq wideAccumulate advanceU)) n a b at h
    cases h with
    | seq hq hrest =>
      cases hrest with
      | seq ha hu =>
        exact ⟨_, _, _, _, _, rfl, hq, ha, hu⟩
  · rintro ⟨nq, na, nu, queried, summed, hn, hq, ha, hu⟩
    subst n
    change StructuredCalls.Eval
      (.seq buildQuery (.seq wideAccumulate advanceU)) (nq + (na + nu)) a b
    exact StructuredCalls.Eval.seq hq (StructuredCalls.Eval.seq ha hu)

/-- Exact source-level factorization of one completed coefficient row. -/
theorem row_eval_iff (n : ℕ) (a b : StructuredCalls.State 8 40) :
    StructuredCalls.Eval row n a b ↔
      ∃ (ns ni nf : ℕ) (seeded accumulated : StructuredCalls.State 8 40),
        n = ns + (ni + nf) ∧
        StructuredCalls.Eval startRow ns a seeded ∧
        StructuredCalls.Eval inner ni seeded accumulated ∧
        StructuredCalls.Eval finishRow nf accumulated b := by
  constructor
  · intro h
    change StructuredCalls.Eval (.seq startRow (.seq inner finishRow)) n a b at h
    cases h with
    | seq hs hrest =>
      cases hrest with
      | seq hi hf =>
        exact ⟨_, _, _, _, _, rfl, hs, hi, hf⟩
  · rintro ⟨ns, ni, nf, seeded, accumulated, hn, hs, hi, hf⟩
    subst n
    change StructuredCalls.Eval
      (.seq startRow (.seq inner finishRow)) (ns + (ni + nf)) a b
    exact StructuredCalls.Eval.seq hs (StructuredCalls.Eval.seq hi hf)

/-- The actual source's U controller pays exactly two steps per slot callback,
    plus two startup/termination steps. This applies only to a *Visits*
    witness, which includes the source callback's counter preservation. -/
theorem inner_visits_exact {costs : List ℕ} {n : ℕ}
    {a b : StructuredCalls.State 8 40}
    (h : UnaryForPrograms.Visits innerPorts slot costs n a b) :
    StructuredCalls.Eval inner n a b ∧
      costs.length = (a.stacks innerPorts.counter).length ∧
      b.stacks innerPorts.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 := by
  obtain ⟨hlen, hempty, hcost⟩ := h.bounds
  exact ⟨h.eval, hlen, hempty, hcost⟩

/-- The original Z controller obeys the same exact overhead formula, with
    row callback costs. Runtime outer-visit count is not a static label count. -/
theorem outer_visits_exact {costs : List ℕ} {n : ℕ}
    {a b : StructuredCalls.State 8 40}
    (h : UnaryForPrograms.Visits outerPorts row costs n a b) :
    StructuredCalls.Eval outer n a b ∧
      costs.length = (a.stacks outerPorts.counter).length ∧
      b.stacks outerPorts.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 := by
  obtain ⟨hlen, hempty, hcost⟩ := h.bounds
  exact ⟨h.eval, hlen, hempty, hcost⟩

/-- Likewise for the source's all-false mask preparation, which is sequential
    with outer traversal rather than inside every row. -/
theorem mask_visits_exact {costs : List ℕ} {n : ℕ}
    {a b : StructuredCalls.State 8 40}
    (h : UnaryForPrograms.Visits maskPorts (wpush 34 false) costs n a b) :
    StructuredCalls.Eval maskLoop n a b ∧
      costs.length = (a.stacks maskPorts.counter).length ∧
      b.stacks maskPorts.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 := by
  obtain ⟨hlen, hempty, hcost⟩ := h.bounds
  exact ⟨h.eval, hlen, hempty, hcost⟩

/-- The row's exact cost exposes *only* source callback costs and controller
    overhead; the numerical work inside each slot is not hidden or free. -/
theorem row_eval_from_inner_visits
    {seedCost loopCost finishCost : ℕ} {costs : List ℕ}
    {initial seeded accumulated final : StructuredCalls.State 8 40}
    (hs : StructuredCalls.Eval startRow seedCost initial seeded)
    (hv : UnaryForPrograms.Visits innerPorts slot costs loopCost seeded accumulated)
    (hf : StructuredCalls.Eval finishRow finishCost accumulated final) :
    StructuredCalls.Eval row
      (seedCost + (costs.sum + 2 * costs.length + 2 + finishCost))
      initial final := by
  have hrow : StructuredCalls.Eval row
      (seedCost + (loopCost + finishCost)) initial final := by
    exact StructuredCalls.Eval.seq hs (StructuredCalls.Eval.seq hv.eval hf)
  have hcost := hv.bounds.2.2
  rw [hcost] at hrow
  exact hrow

/-- Source-defined end-to-end *control shell* cost, given source callbacks:
    prepare + all row costs + two outer control steps per row + finish.
    The premise is an actual Visits trace, not an invented list of costs. -/
theorem readout_eval_from_outer_visits
    {prepareCost outerCost finishCost : ℕ} {costs : List ℕ}
    {initial prepared iterated final : StructuredCalls.State 8 40}
    (hp : StructuredCalls.Eval prepare prepareCost initial prepared)
    (hv : UnaryForPrograms.Visits outerPorts row costs outerCost prepared iterated)
    (hf : StructuredCalls.Eval finish finishCost iterated final) :
    StructuredCalls.Eval command
      (prepareCost + (costs.sum + 2 * costs.length + 2 + finishCost))
      initial final := by
  have hreadout : StructuredCalls.Eval command
      (prepareCost + (outerCost + finishCost)) initial final := by
    exact StructuredCalls.Eval.seq hp (StructuredCalls.Eval.seq hv.eval hf)
  have hcost := hv.bounds.2.2
  rw [hcost] at hreadout
  exact hreadout

end OAI.Algorithms.SubexponentialSAT.ReadoutRow
