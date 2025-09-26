import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple swap operation
-- </vc-helpers>

-- <vc-definitions>
def SwapSimultaneous (X Y : Int) : Int × Int :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapSimultaneous_spec (X Y : Int) :
let (x, y) := SwapSimultaneous X Y
x = Y ∧ y = X :=
by simp [SwapSimultaneous]
-- </vc-theorems>
