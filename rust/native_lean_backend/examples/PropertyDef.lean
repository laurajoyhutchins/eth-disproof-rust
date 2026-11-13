namespace Property
  /-- A bounded-depth fixed-width recurrence, deliberately using only the
      executable IR subset that the current native backend supports. -/
  partial def hop (fuel x : UInt64) : UInt64 :=
    if fuel == 0 then x
    else
      let updated := if x < 3 then x * 3 + 1 else x * 5 + 7
      (hop (fuel - 1) updated) + 11
end Property
