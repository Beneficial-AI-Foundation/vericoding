import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def Swap (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem Swap_spec (X Y : Int) :
let (x, y) := Swap X Y
x = Y ∧ y = X :=
by
  simpa [Swap] using And.intro rfl rfl
-- </vc-theorems>
