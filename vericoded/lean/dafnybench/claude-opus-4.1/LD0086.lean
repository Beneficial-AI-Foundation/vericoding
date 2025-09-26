import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple swap function
-- </vc-helpers>

-- <vc-definitions>
def SwapArithmetic (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapArithmetic_spec (X Y : Int) :
let (x, y) := SwapArithmetic X Y
x = Y ∧ y = X :=
by
  simp [SwapArithmetic]
-- </vc-theorems>
