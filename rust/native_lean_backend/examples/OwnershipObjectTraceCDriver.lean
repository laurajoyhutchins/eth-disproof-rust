import OwnershipObjectTraceKernels

-- Borrowed observational FFI, present ONLY in this driver, never in the
-- source definitions compiled by the Rust backend.
@[extern "lr_object_trace_id"] opaque traceId
  (x : @& OwnershipObjectTrace.Token) : UInt64
@[extern "lr_object_trace_rc"] opaque traceCount
  (x : @& OwnershipObjectTrace.Token) : UInt64

def main (args : List String) : IO Unit := do
  let words := args.toArray
  if words.size != 2 then
    throw <| IO.userError "expected two runtime Nat inputs"
  let some first := words[0]!.toNat?
    | throw <| IO.userError "first argument is not a Nat"
  let some second := words[1]!.toNat?
    | throw <| IO.userError "second argument is not a Nat"
  let a := OwnershipObjectTrace.create first
  IO.println s!"TRACE create {traceId a} {traceCount a}"
  let same := OwnershipObjectTrace.identity a
  IO.println s!"TRACE direct {traceId a} {traceCount a} {traceId same} {traceCount same}"
  let b := OwnershipObjectTrace.create second
  IO.println s!"TRACE second {traceId b} {traceCount b}"
  let left := OwnershipObjectTrace.select true same b
  IO.println s!"TRACE branch-left {traceId same} {traceCount same} {traceId left} {traceCount left} {traceId b} {traceCount b}"
  let right := OwnershipObjectTrace.select false same b
  IO.println s!"TRACE branch-right {traceId same} {traceCount same} {traceId right} {traceCount right} {traceId b} {traceCount b}"
  let captured := OwnershipObjectTrace.throughClosure left
  IO.println s!"TRACE closure {traceId left} {traceCount left} {traceId captured} {traceCount captured}"
