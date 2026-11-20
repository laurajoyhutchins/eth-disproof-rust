import Lean

/-!
# Restricted effects and source-operation order

This is a deterministic abstraction of a single-threaded reference-count
machine without allocation, release, destructor cascades, or faults. A
resource index denotes a proven allocation identity, never merely an IR
variable number. This model does not establish Lean C runtime fidelity.
-/
namespace ReaderEffectOrder

abbrev Counts := Nat → Nat

def put (h : Counts) (id value : Nat) : Counts :=
  fun other => if other == id then value else h other

@[simp] theorem put_self (h : Counts) (id value : Nat) :
    put h id value id = value := by simp [put]

@[simp] theorem put_other (h : Counts) (id other value : Nat)
    (hne : other ≠ id) : put h id value other = h other := by
  simp [put, hne]

def retain (h : Counts) (id : Nat) : Counts :=
  put h id (h id + 1)

def shared (h : Counts) (id : Nat) : Bool :=
  decide (1 < h id)

theorem retain_preserves_other_count (h : Counts) (id other : Nat)
    (distinct : other ≠ id) : retain h id other = h other := by
  simp [retain, distinct]

theorem retain_preserves_other_sharing (h : Counts) (id other : Nat)
    (distinct : other ≠ id) : shared (retain h id) other = shared h other := by
  simp [shared, retain_preserves_other_count, distinct]

theorem retain_commutes (h : Counts) (a b : Nat) (distinct : a ≠ b) :
    retain (retain h a) b = retain (retain h b) a := by
  funext k
  by_cases hka : k = a
  · subst k
    simp [retain, put, distinct]
  · by_cases hkb : k = b
    · subst k
      simp [retain, put, Ne.symm distinct]
    · simp [retain, put, hka, hkb]

theorem retaining_once_changes_sharing (id : Nat) :
    shared (retain (fun _ => 1) id) id = true ∧
    shared (fun _ => 1) id = false := by
  simp [shared, retain, put]

inductive Event where
  | retain : Nat → Event
  | observe : Nat → Event
  deriving Repr, DecidableEq

def step (event : Event) (h : Counts) : Counts × Option Bool :=
  match event with
  | .retain id => (retain h id, none)
  | .observe id => (h, some (shared h id))

def run : List Event → Counts → Counts × List Bool
  | [], h => (h, [])
  | event :: rest, h =>
      let (next, observed) := step event h
      let (final, later) := run rest next
      (final, match observed with
        | none => later
        | some value => value :: later)

/-- A source retain and sharing observation commute when their **actual
allocation identities** are provably distinct. -/
theorem independent_retain_observe (h : Counts) (a b : Nat)
    (distinct : a ≠ b) :
    run [.retain a, .observe b] h = run [.observe b, .retain a] h := by
  simp [run, step, retain_preserves_other_sharing, Ne.symm distinct]

/-- If a bounded emitter preserves every modeled event in exact source
order, the modeled state and ordered observations are identical. This is
*not* a theorem that an emitter or runtime actually preserves those events. -/
theorem replay_exact_order (source emitted : List Event) (h : Counts)
    (same : source = emitted) : run source h = run emitted h := by
  rw [same]

/-- A tested negative witness: a retain followed by a sharing observation
cannot generally be reordered on the same allocation. -/
theorem observed_retain_cannot_swap (id : Nat) :
    (run [.retain id, .observe id] (fun _ => 1)).2 ≠
      (run [.observe id, .retain id] (fun _ => 1)).2 := by
  simp [run, step, retain, put, shared]

end ReaderEffectOrder

#print axioms ReaderEffectOrder.retain_preserves_other_count
#print axioms ReaderEffectOrder.retain_preserves_other_sharing
#print axioms ReaderEffectOrder.retain_commutes
#print axioms ReaderEffectOrder.retaining_once_changes_sharing
#print axioms ReaderEffectOrder.independent_retain_observe
#print axioms ReaderEffectOrder.replay_exact_order
#print axioms ReaderEffectOrder.observed_retain_cannot_swap
