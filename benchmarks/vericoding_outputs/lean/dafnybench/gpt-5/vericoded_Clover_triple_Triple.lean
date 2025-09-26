import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper declarations needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def Triple (x : Int) : Int :=
3 * x
-- </vc-definitions>

-- <vc-theorems>
theorem Triple_spec (x : Int) : Triple x = 3 * x :=
rfl
-- </vc-theorems>
