import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helper functions needed for this simple implementation
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
