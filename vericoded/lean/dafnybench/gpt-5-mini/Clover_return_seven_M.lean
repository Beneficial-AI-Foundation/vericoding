import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def const7 : Int := 7
-- LLM HELPER
theorem const7_spec : const7 = 7 := rfl
-- </vc-helpers>

-- <vc-definitions>
def M (x : Int) : Int :=
const7
-- </vc-definitions>

-- <vc-theorems>
theorem M_spec (x : Int) : M x = 7 :=
by rfl
-- </vc-theorems>
