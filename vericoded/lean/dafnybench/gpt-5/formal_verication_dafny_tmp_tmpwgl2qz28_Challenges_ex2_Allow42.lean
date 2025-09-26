import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required
-- </vc-helpers>

-- <vc-definitions>
def Allow42 (x : Int) (y : Int) : Int × Bool :=
if h : y = 42 then (0, true) else (x / (42 - y), false)
-- </vc-definitions>

-- <vc-theorems>
theorem Allow42_spec (x y : Int) :
let (z, err) := Allow42 x y
(y ≠ 42 → z = x/(42-y) ∧ err = false) ∧
(y = 42 → z = 0 ∧ err = true) :=
by
  by_cases h : y = 42
  · subst h
    simpa [Allow42]
  · simpa [Allow42, h]
-- </vc-theorems>
