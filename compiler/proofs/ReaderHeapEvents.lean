import Lean

/-!
# Bounded source-heap event semantics

A source object has a stable allocation ID, an owned reference count,
and an ordered list of owned heap children. The event executor models
observed allocations and explicit source retains/releases; a final release
recursively decrements owned children. A live Rust Rc alias is deliberately
not a source reference.

The fuel bounds the destructor walk, and malformed, dangling, duplicate,
underflow, or unobservable events fail closed. \`seed\` describes an already
constructed source graph at the first observation boundary: it does NOT
assert that observing an allocation is the real allocator's timestamp.

This is a specified event machine, not yet a formal correctness theorem
about the Lean C runtime, the Reader's Rust source ledger, or LLVM.
-/

namespace ReaderHeapEvents

structure Node where
  refs : Nat
  children : List Nat
  deriving Repr, DecidableEq

abbrev Heap := Nat → Option Node

def put (heap : Heap) (id : Nat) (node : Option Node) : Heap :=
  fun x => if x == id then node else heap x

@[simp] theorem put_self (h : Heap) (id : Nat) (n : Option Node) :
    put h id n id = n := by simp [put]

@[simp] theorem put_other (h : Heap) (id other : Nat) (n : Option Node)
    (hne : other ≠ id) : put h id n other = h other := by
  simp [put, beq_iff_eq, hne]

def empty : Heap := fun _ => none

/-- Add one observed live allocation; every owned child must already be
seeded. This chooses a topological replay order, not allocator chronology. -/
def seed (h : Heap) (id refs : Nat) (children : List Nat) : Option Heap :=
  if refs == 0 || (h id).isSome ||
      !children.all (fun child => (h child).isSome) then none
  else some (put h id (some ⟨refs, children⟩))

/-- An actual retained source reference, not a cloned Rust Rc handle. -/
def retain (h : Heap) (id : Nat) : Option Heap :=
  match h id with
  | none => none
  | some n => some (put h id (some { n with refs := n.refs + 1 }))

/-- Drop an owned reference; the last release recursively releases every
owned child of the destroyed constructor. Fuel limits even malformed
cyclic input, so the replay cannot diverge. -/
def release : Nat → Heap → Nat → Option Heap
  | 0, _, _ => none
  | fuel + 1, h, id =>
      match h id with
      | none => none
      | some n =>
          if n.refs == 0 then none
          else if n.refs > 1 then
            some (put h id (some { n with refs := n.refs - 1 }))
          else
            n.children.foldlM
              (fun acc child => release fuel acc child)
              (put h id none)

/-- A source-physical boundary assertion, checked *after* an operation.
A destroyed object is never dereferenced by the physical observer. -/
inductive Event where
  | seed : Nat → Nat → List Nat → Event
  | retain : Nat → Event
  | release : Nat → Event
  | observe : Nat → Nat → Event
  deriving Repr, DecidableEq

def step (fuel : Nat) (h : Heap) : Event → Option Heap
  | .seed id refs children => seed h id refs children
  | .retain id => retain h id
  | .release id => release fuel h id
  | .observe id count =>
      match h id with
      | some n => if n.refs == count && count > 0 then some h else none
      | none => none

def run (fuel : Nat) : List Event → Heap → Option Heap
  | [], h => some h
  | e :: es, h => do
      let next ← step fuel h e
      run fuel es next

theorem retain_requires_live (h : Heap) (id : Nat)
    (hdead : h id = none) : retain h id = none := by
  simp [retain, hdead]

theorem release_requires_live (fuel : Nat) (h : Heap) (id : Nat)
    (hdead : h id = none) : release fuel h id = none := by
  cases fuel with
  | zero => rfl
  | succ n => simp [release, hdead]

theorem release_last_leaf (fuel : Nat) (h : Heap) (id : Nat)
    (hnode : h id = some ⟨1, []⟩) :
    release (fuel + 1) h id = some (put h id none) := by
  simp [release, hnode]

theorem retain_changes_only_named_object (h h' : Heap) (id other : Nat)
    (ok : retain h id = some h') (different : other ≠ id) :
    h' other = h other := by
  unfold retain at ok
  cases hn : h id with
  | none => simp [hn] at ok
  | some n =>
      simp [hn] at ok
      subst h'
      simp [put, different]

theorem seed_changes_only_named_object (h h' : Heap)
    (id refs : Nat) (children : List Nat)
    (ok : seed h id refs children = some h') (other : Nat)
    (different : other ≠ id) :
    h' other = h other := by
  unfold seed at ok
  split at ok
  · simp at ok
  · simp at ok
    subst h'
    simp [put, different]

theorem observation_preserves_heap (fuel : Nat) (h h' : Heap)
    (id count : Nat)
    (ok : step fuel h (.observe id count) = some h') :
    h' = h := by
  simp only [step] at ok
  cases hn : h id with
  | none => simp [hn] at ok
  | some n =>
      split at ok
      · cases ok
        rfl
      · cases ok

theorem observation_requires_live (fuel : Nat) (h : Heap)
    (id count : Nat) (dead : h id = none) :
    step fuel h (.observe id count) = none := by
  simp [step, dead]

/-- A five-object source graph. The two retained descendants each have
two references before releasing the root. The final root release cascades
through the intermediate fork and its other leaf, while preserving one
independent credit each for grandchild and sibling. -/
def nested : Heap :=
  put (put (put (put (put empty
    3 (some ⟨1, []⟩))
    5 (some ⟨1, []⟩))
    2 (some ⟨1, [3, 5]⟩))
    4 (some ⟨1, []⟩))
    1 (some ⟨1, [2, 4]⟩)

def nestedEvents : List Event := [
  .observe 1 1, .observe 2 1, .observe 3 1,
  .observe 4 1, .observe 5 1,
  .retain 3, .observe 3 2,
  .retain 4, .observe 4 2,
  .release 1,
  .observe 3 1, .observe 4 1
]

theorem nested_release_keeps_only_explicit_descendants :
    (run 10 nestedEvents nested).isSome = true ∧
    (run 10 nestedEvents nested).bind (fun h => h 1) = none ∧
    (run 10 nestedEvents nested).bind (fun h => h 2) = none ∧
    (run 10 nestedEvents nested).bind (fun h => h 5) = none ∧
    (run 10 nestedEvents nested).bind (fun h => h 3) = some ⟨1, []⟩ ∧
    (run 10 nestedEvents nested).bind (fun h => h 4) = some ⟨1, []⟩ := by
  decide

/-- A duplicate allocation is refused; address/ID reuse is not silently
taken as a new source object while the first allocation remains live. -/
theorem seed_duplicate_is_refused :
    seed nested 3 1 [] = none := by decide

theorem release_of_dead_object_is_refused :
    release 10 (put nested 3 none) 3 = none := by decide

/-- A missing source retain cannot be manufactured from the fact that a
Rust Rc allocation might remain resident after source destruction. -/
theorem cannot_retain_source_freed_descendant :
    retain (put nested 3 none) 3 = none := by decide

end ReaderHeapEvents

#print axioms ReaderHeapEvents.retain_requires_live
#print axioms ReaderHeapEvents.release_requires_live
#print axioms ReaderHeapEvents.release_last_leaf
#print axioms ReaderHeapEvents.retain_changes_only_named_object
#print axioms ReaderHeapEvents.seed_changes_only_named_object
#print axioms ReaderHeapEvents.observation_preserves_heap
#print axioms ReaderHeapEvents.observation_requires_live
#print axioms ReaderHeapEvents.nested_release_keeps_only_explicit_descendants
#print axioms ReaderHeapEvents.seed_duplicate_is_refused
#print axioms ReaderHeapEvents.release_of_dead_object_is_refused
#print axioms ReaderHeapEvents.cannot_retain_source_freed_descendant
