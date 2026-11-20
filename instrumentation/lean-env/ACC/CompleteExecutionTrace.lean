import Mathlib
import ACC.ArrayFinishSimulation
import ACC.ArithmeticReceipts

/-!
# Source-bound, ordered complete contraction traces

A trace is not an unordered bag of individually correct arithmetic receipts.
The checker independently reconstructs *every expected call in order*, from
the supplied source weights and certified class labels. It checks the
observed operand words, operation kinds, successful values, and first
overflow refusal, without consuming an untrusted intermediate array.

The simulation below proves that the entire word-level schedule decodes to
the checked integer-array interpreter, including every refusal. The verifier
can therefore check the ordered word trace and source certificate alone;
it no longer needs to evaluate the integer array a second time.

This is finite, input-bound translation validation. It does not prove the
Rust emitter captured real hardware instructions or that the Rust guard
loop implements the Lean indexed guard for all inputs.
-/

namespace ACC.CompleteExecutionTrace

open ACC.ArithmeticReceipts
open ACC.CheckedI128BitVec
open ACC.IndexedRankedCertificate
open ACC.ArrayFinishSimulation
open ACC.ComponentFoldCorrespondence
open ACC.ArrayStepSimulation
open ACC.ArrayScanSimulation
open ACC.CheckedComponentArithmetic

abbrev WordPair := Word × Word

/-- The vertex stream used by Rust's component array scan. -/
def wordItems {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    List (Fin c × WordPair) :=
  (List.finRange n).map fun i =>
    (label i, (weight i false, weight i true))

/-- Model-generated receipts never trust an external reported result. -/
def recorded (kind : Kind) (left right : Word) : Receipt :=
  { kind := kind, left := left, right := right
    observed := expected kind left right }

/-- The atomic per-vertex update logs both multiplications only when the
    first succeeds. No array slot changes until both have succeeded. -/
def scanTrace {c : ℕ} (products : Array WordPair) :
    List (Fin c × WordPair) → List Receipt × Option (Array WordPair)
  | [] => ([], some products)
  | item :: rest =>
      match products[item.1.val]? with
      | none => ([], none)
      | some old =>
          let first := recorded .mul old.1 item.2.1
          match first.observed with
          | none => ([first], none)
          | some zero =>
              let second := recorded .mul old.2 item.2.2
              match second.observed with
              | none => ([first, second], none)
              | some one =>
                  let (later, result) :=
                    scanTrace (products.setIfInBounds item.1.val (zero, one)) rest
                  (first :: second :: later, result)

/-- Exactly one checked addition followed by one checked multiplication for
    each class, stopping at the first refusing operation. -/
def finishTrace {c : ℕ} (products : Array WordPair)
    (acc : Word) : List (Fin c) → List Receipt × Option Word
  | [] => ([], some acc)
  | k :: rest =>
      match products[k.val]? with
      | none => ([], none)
      | some pair =>
          let addition := recorded .add pair.1 pair.2
          match addition.observed with
          | none => ([addition], none)
          | some factor =>
              let multiplication := recorded .mul acc factor
              match multiplication.observed with
              | none => ([addition, multiplication], none)
              | some next =>
                  let (later, result) := finishTrace products next rest
                  (addition :: multiplication :: later, result)

/-- The complete deterministic arithmetic schedule, including refusal.
    This reconstructs the expected trace independently of Rust's emitter. -/
def expectedExecution {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    List Receipt × Option Word :=
  let one : Word := BitVec.ofInt 128 1
  let (scan, finalProducts) :=
    scanTrace (Array.replicate c (one, one)) (wordItems label weight)
  match finalProducts with
  | none => (scan, none)
  | some products =>
      let (finish, result) := finishTrace products one (List.finRange c)
      (scan ++ finish, result)


/-- Decode an entire concrete word-array state, preserving slot order. -/
def decodePair (pair : WordPair) : ℤ × ℤ :=
  (pair.1.toInt, pair.2.toInt)

def decodeArray (pairs : Array WordPair) : Array (ℤ × ℤ) :=
  pairs.map decodePair

/-- An ordered word-item stream decodes to the same vertex-major stream
    used by the previously proved checked integer-array interpreter. -/
theorem wordItems_decode {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    (wordItems label weight).map
      (fun item => (item.1, decodePair item.2)) =
        sourceItems label (fun i bit => (weight i bit).toInt) := by
  simp [wordItems, sourceItems, List.map_map, Function.comp_def, decodePair]

/-- The *result* of every source-ordered word scan is identical after
    decoding to the checked integer array scan, even when the first or
    second multiplication refuses. Earlier successful updates are retained
    on both sides, and a failed vertex never writes a half-updated slot. -/
theorem scanTrace_refines {c : ℕ}
    (products : Array WordPair)
    (items : List (Fin c × WordPair)) :
    Option.map decodeArray (scanTrace products items).2 =
      checkedArrayScanFrom (decodeArray products)
        (items.map (fun item => (item.1, decodePair item.2))) := by
  induction items generalizing products with
  | nil =>
      simp [scanTrace, checkedArrayScanFrom, decodeArray]
  | cons item rest ih =>
      cases hget : products[item.1.val]? with
      | none =>
          have hgetInt :
              (decodeArray products)[item.1.val]? = none := by
            simpa [decodeArray] using
              congrArg (Option.map decodePair) hget
          simp [scanTrace, hget, checkedArrayScanFrom,
            checkedArrayStep, hgetInt]
      | some old =>
          have hgetInt :
              (decodeArray products)[item.1.val]? =
                some (decodePair old) := by
            simpa [decodeArray] using
              congrArg (Option.map decodePair) hget
          cases hz : checkedWordMul old.1 item.2.1 with
          | none =>
              have hzInt :
                  checkedMul old.1.toInt item.2.1.toInt = none := by
                have hh := checkedWordMul_eq_checkedMul old.1 item.2.1
                rw [hz] at hh
                simpa using hh.symm
              simp [scanTrace, hget, recorded, expected, hz,
                checkedArrayScanFrom, checkedArrayStep, hgetInt,
                decodePair, hzInt]
          | some zero =>
              have hzInt :
                  checkedMul old.1.toInt item.2.1.toInt =
                    some zero.toInt := by
                have hh := checkedWordMul_eq_checkedMul old.1 item.2.1
                rw [hz] at hh
                simpa using hh.symm
              cases ho : checkedWordMul old.2 item.2.2 with
              | none =>
                  have hoInt :
                      checkedMul old.2.toInt item.2.2.toInt = none := by
                    have hh := checkedWordMul_eq_checkedMul old.2 item.2.2
                    rw [ho] at hh
                    simpa using hh.symm
                  simp [scanTrace, hget, recorded, expected, hz, ho,
                    checkedArrayScanFrom, checkedArrayStep, hgetInt,
                    decodePair, hzInt, hoInt]
              | some one =>
                  have hoInt :
                      checkedMul old.2.toInt item.2.2.toInt =
                        some one.toInt := by
                    have hh := checkedWordMul_eq_checkedMul old.2 item.2.2
                    rw [ho] at hh
                    simpa using hh.symm
                  have hnext :
                      decodeArray
                          (products.setIfInBounds item.1.val (zero, one)) =
                        (decodeArray products).setIfInBounds item.1.val
                          (zero.toInt, one.toInt) := by
                    simp [decodeArray, decodePair]
                  simpa [scanTrace, hget, recorded, expected, hz, ho,
                    checkedArrayScanFrom, checkedArrayStep, hgetInt,
                    decodePair, hzInt, hoInt, hnext] using
                    ih (products.setIfInBounds item.1.val (zero, one))

/-- The immutable class-major word finalizer has the same optional result
    as integer finalization after decoding, including both possible
    arithmetic refusals, and independently of the initial accumulator. -/
theorem finishTrace_refines {c : ℕ}
    (products : Array WordPair) (acc : Word)
    (classes : List (Fin c)) :
    Option.map BitVec.toInt (finishTrace products acc classes).2 =
      checkedArrayFinishFrom (decodeArray products) acc.toInt classes := by
  induction classes generalizing acc with
  | nil =>
      simp [finishTrace, checkedArrayFinishFrom]
  | cons k rest ih =>
      cases hget : products[k.val]? with
      | none =>
          have hgetInt : (decodeArray products)[k.val]? = none := by
            simpa [decodeArray] using
              congrArg (Option.map decodePair) hget
          simp [finishTrace, hget, checkedArrayFinishFrom, hgetInt]
      | some pair =>
          have hgetInt :
              (decodeArray products)[k.val]? =
                some (decodePair pair) := by
            simpa [decodeArray] using
              congrArg (Option.map decodePair) hget
          cases ha : checkedWordAdd pair.1 pair.2 with
          | none =>
              have haInt :
                  checkedAdd pair.1.toInt pair.2.toInt = none := by
                have hh := checkedWordAdd_eq_checkedAdd pair.1 pair.2
                rw [ha] at hh
                simpa using hh.symm
              simp [finishTrace, hget, recorded, expected, ha,
                checkedArrayFinishFrom, hgetInt, decodePair, haInt]
          | some factor =>
              have haInt :
                  checkedAdd pair.1.toInt pair.2.toInt =
                    some factor.toInt := by
                have hh := checkedWordAdd_eq_checkedAdd pair.1 pair.2
                rw [ha] at hh
                simpa using hh.symm
              cases hm : checkedWordMul acc factor with
              | none =>
                  have hmInt :
                      checkedMul acc.toInt factor.toInt = none := by
                    have hh := checkedWordMul_eq_checkedMul acc factor
                    rw [hm] at hh
                    simpa using hh.symm
                  simp [finishTrace, hget, recorded, expected, ha, hm,
                    checkedArrayFinishFrom, hgetInt, decodePair, haInt, hmInt]
              | some next =>
                  have hmInt :
                      checkedMul acc.toInt factor.toInt =
                        some next.toInt := by
                    have hh := checkedWordMul_eq_checkedMul acc factor
                    rw [hm] at hh
                    simpa using hh.symm
                  simpa [finishTrace, hget, recorded, expected, ha, hm,
                    checkedArrayFinishFrom, hgetInt, decodePair, haInt,
                    hmInt] using ih next

/-- Universal exact Option-valued correspondence for the complete ordered
    word replay. No successful-result assumption, no separately checked
    integer array, and no premise about a submitted trace. In particular,
    word-level overflow refusal occurs iff the integer array interpreter
    refuses at precisely the same position of the execution schedule. -/
theorem expectedExecution_refines {n c : ℕ}
    (label : Fin n → Fin c) (weight : Fin n → Bool → Word) :
    Option.map BitVec.toInt (expectedExecution label weight).2 =
      checkedArrayContraction
        (sourceItems label (fun i bit => (weight i bit).toInt)) := by
  let one : Word := BitVec.ofInt 128 1
  let initial : Array WordPair := Array.replicate c (one, one)
  let items : List (Fin c × WordPair) := wordItems label weight
  have hinit : decodeArray initial = Array.replicate c (1, 1) := by
    simp [decodeArray, decodePair, initial, one]
  have hitems :
      items.map (fun item => (item.1, decodePair item.2)) =
        sourceItems label (fun i bit => (weight i bit).toInt) :=
    wordItems_decode label weight
  have hscan := scanTrace_refines initial items
  rw [hinit, hitems] at hscan
  cases hp : scanTrace initial items with
  | mk receipts scanResult =>
      have hs :
          Option.map decodeArray scanResult =
            checkedArrayScanFrom (Array.replicate c (1, 1))
              (sourceItems label (fun i bit => (weight i bit).toInt)) := by
        simpa only [hp, Prod.snd] using hscan
      cases scanResult with
      | none =>
          have hsnone :
              checkedArrayScanFrom (Array.replicate c (1, 1))
                (sourceItems label (fun i bit => (weight i bit).toInt)) =
                  none := by
            simpa using hs.symm
          simp [expectedExecution, one, initial, items, hp,
            checkedArrayContraction, hsnone]
      | some products =>
          have hssome :
              checkedArrayScanFrom (Array.replicate c (1, 1))
                (sourceItems label (fun i bit => (weight i bit).toInt)) =
                  some (decodeArray products) := by
            simpa using hs.symm
          have hf :
              Option.map BitVec.toInt
                  (finishTrace products one (List.finRange c)).2 =
                checkedArrayFinishFrom (decodeArray products)
                  1 (List.finRange c) := by
            simpa [one] using
              finishTrace_refines products one (List.finRange c)
          simpa [expectedExecution, one, initial, items, hp,
            checkedArrayContraction, hssome] using hf


/-- The finite checker validates the source-edge certificate, every reported
    operation, and *the complete ordered replay*. Integer-array agreement
    follows by theorem and is not separately recomputed at runtime. -/
def checkComplete {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word) : Bool :=
  (checkIndexed edges label root sourceIndex rank && checkTrace trace) &&
  decide (expectedExecution label weight = (trace, reported))

/-- An accepted witness is the whole reconstructed schedule. In particular
    dropping, reordering, or appending any operation changes the answer
    of the checker unless it is the *same* trace. -/
theorem checkComplete_schedule {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace reported = true) :
    expectedExecution label weight = (trace, reported) := by
  simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Every accepted reported operation is valid against the signed-word
    specification, including all overflow refusals. -/
theorem checkComplete_receipts {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace reported = true) :
    ∀ receipt ∈ trace,
      receipt.observed =
        expected receipt.kind receipt.left receipt.right := by
  simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkTrace_sound trace h.1.2

/-- The full replay *proves*, rather than separately checks, the exact
    integer-array result, even when a word-level operation refuses. -/
theorem checkComplete_result {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (reported : Option Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace reported = true) :
    checkedArrayContraction
      (sourceItems label (fun i bit => (weight i bit).toInt)) =
        reported.map BitVec.toInt := by
  have hs := checkComplete_schedule
    edges label root sourceIndex rank weight trace reported h
  have hr := expectedExecution_refines label weight
  rw [hs] at hr
  simpa using hr.symm

/-- Kernel-level finite-execution soundness for a successful witness:
    the accepted word is the *literal source-edge count*. The only dynamic
    arithmetic authority is the signed-word replay. Exact integer-array
    correspondence is now a universal theorem, not an acceptance guard. -/
theorem checkComplete_success_sound {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) (weight : Fin n → Bool → Word)
    (trace : List Receipt) (value : Word)
    (h : checkComplete edges label root sourceIndex rank
      weight trace (some value) = true) :
    value.toInt =
      (∑ x : {x : Fin n → Bool // ∀ e ∈ edges, x e.1 = x e.2},
        ∏ i : Fin n, (weight i (x.1 i)).toInt) := by
  have hcert :
      checkIndexed edges label root sourceIndex rank = true := by
    simp only [checkComplete, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  have hresult := checkComplete_result
    edges label root sourceIndex rank weight trace (some value) h
  exact checkedArrayContraction_source_edges
    edges label root sourceIndex rank
    (fun i bit => (weight i bit).toInt) value.toInt
    hcert (by simpa using hresult)

/-- Zero vertices and zero classes require no reported operations. -/
example :
    expectedExecution (n := 0) (c := 0)
      (fun i => i.elim0) (fun i _ => i.elim0) =
        ([], some (BitVec.ofInt 128 1)) := by decide

#print axioms ACC.CompleteExecutionTrace.scanTrace_refines
#print axioms ACC.CompleteExecutionTrace.finishTrace_refines
#print axioms ACC.CompleteExecutionTrace.expectedExecution_refines
#print axioms ACC.CompleteExecutionTrace.checkComplete_result
#print axioms ACC.CompleteExecutionTrace.checkComplete_schedule
#print axioms ACC.CompleteExecutionTrace.checkComplete_receipts
#print axioms ACC.CompleteExecutionTrace.checkComplete_success_sound

end ACC.CompleteExecutionTrace
