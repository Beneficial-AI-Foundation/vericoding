import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- Helper definitions if needed
-- </vc-helpers>

-- <vc-definitions>
def Swap (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem Swap_spec (X Y : Int) :
let (x, y) := Swap X Y
x = Y ∧ y = X :=
by simp [Swap]
-- </vc-theorems>
