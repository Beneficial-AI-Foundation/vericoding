import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def append (a : Array Int) (b : Int) : Array Int :=
a.push b
-- </vc-definitions>

-- <vc-theorems>
theorem append_spec (a : Array Int) (b : Int) :
append a b = a.push b :=
rfl
-- </vc-theorems>
