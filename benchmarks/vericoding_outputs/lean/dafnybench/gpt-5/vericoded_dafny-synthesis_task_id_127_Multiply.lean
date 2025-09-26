import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Trivial helper so the helpers section is nonempty. -/
def idInt (x : Int) : Int := x
-- </vc-helpers>

-- <vc-definitions>
def Multiply (a b : Int) : Int :=
a * b
-- </vc-definitions>

-- <vc-theorems>
theorem Multiply_spec (a b : Int) :
Multiply a b = a * b :=
rfl
-- </vc-theorems>
