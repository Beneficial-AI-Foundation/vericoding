import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def Allow42 (x : Int) (y : Int) : Int × Bool :=
if y = 42 then (0, true) else (x / (42 - y), false)
-- </vc-definitions>

-- <vc-theorems>
theorem Allow42_spec (x y : Int) :
let (z, err) := Allow42 x y
(y ≠ 42 → z = x/(42-y) ∧ err = false) ∧
(y = 42 → z = 0 ∧ err = true) :=
by
  by_cases h : y = 42
  · simp [Allow42, h]
  · simp [Allow42, h]
-- </vc-theorems>
