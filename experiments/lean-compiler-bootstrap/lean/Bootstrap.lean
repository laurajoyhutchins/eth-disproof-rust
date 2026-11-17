import Lungo
import Lean.Compiler.IR.Basic

/-!
Upstream Lean's actual compiled IRType predicates. The fixture adds a numeric
facade so Rust does not expose the compiler's internal inductive types.
Lean.Compiler.IR.Basic itself is neither copied nor edited.
-/

namespace Bootstrap

def tag_type (tag : UInt8) : Lean.IR.IRType :=
  match tag.toNat with
  | 0 => .uint8
  | 1 => .uint16
  | 2 => .uint32
  | 3 => .uint64
  | 4 => .usize
  | 5 => .float
  | 6 => .float32
  | 7 => .object
  | 8 => .tobject
  | 9 => .tagged
  | 10 => .void
  | 11 => .erased
  | _ => .struct none #[.uint64]

def probe_scalar (tag : UInt8) : Bool :=
  Lean.IR.IRType.isScalar (tag_type tag)

def probe_object (tag : UInt8) : Bool :=
  Lean.IR.IRType.isObj (tag_type tag)

def probe_possible_ref (tag : UInt8) : Bool :=
  Lean.IR.IRType.isPossibleRef (tag_type tag)

def probe_definite_ref (tag : UInt8) : Bool :=
  Lean.IR.IRType.isDefiniteRef (tag_type tag)

def probe_erased (tag : UInt8) : Bool :=
  Lean.IR.IRType.isErased (tag_type tag)

def probe_boxed_tagged (tag : UInt8) : Bool :=
  Lean.IR.IRType.boxed (tag_type tag) == .tagged

/-- Scalar compiler IR types cannot simultaneously be possible heap references. -/
@[lungo_claim "lungo.law" subject probe_scalar]
theorem scalar_not_reference (tag : UInt8) :
    probe_scalar tag = true → probe_possible_ref tag = false := by
  cases h : tag_type tag <;>
    simp [probe_scalar, probe_possible_ref, h,
      Lean.IR.IRType.isScalar, Lean.IR.IRType.isPossibleRef]

end Bootstrap
