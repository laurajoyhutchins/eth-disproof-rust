import LeanNativeOwnershipAudit
import RuntimeHeapDelKernels

-- The exact six unchanged source declarations used by the established
-- final-IR probe; no reification or manually fabricated IR is used.
#lean_native_ownership_audit [
  RuntimeHeapDel.rebuild,
  RuntimeHeapDel.rebuildOrDiscard,
  RuntimeHeapDel.rebuildOrExtract,
  RuntimeHeapDel.rebuildThenExtract,
  RuntimeHeapDel.rebuildOrDiscardByPayload,
  RuntimeHeapDel.rebuildOrExtractByPayload
] to "artifacts/lean-native-ownership"

-- Important: the native scalar *code generator* must continue to refuse
-- ownership-sensitive heap declarations. The separate manifest audit is
-- not permission to silently lower these operations.
