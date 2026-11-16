import LCNFCapture

-- The meta-level installer must be compiled in its defining module before
-- Lean's interpreter evaluates it. Applying [cpass] to an imported installer
-- avoids evaluating an as-yet uncompiled same-module declaration.
attribute [cpass] NativeRust.LCNFCapture.installObserver
