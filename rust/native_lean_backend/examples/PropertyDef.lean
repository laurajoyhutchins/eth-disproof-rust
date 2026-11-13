namespace Property
  /-- A bounded-depth fixed-width recurrence deliberately limited to supported
      executable IR (branches return directly, with no join-point lowering). -/
  partial def hop (fuel x : UInt64) : UInt64 :=
    if fuel == 0 then x
    else if x < 3 then (hop (fuel - 1) (x * 3 + 1)) + 11
    else (hop (fuel - 1) (x * 5 + 7)) + 11
end Property
