import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple implementation
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
