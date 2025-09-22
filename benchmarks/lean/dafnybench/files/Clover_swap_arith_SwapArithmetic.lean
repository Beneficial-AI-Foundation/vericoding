-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SwapArithmetic (X Y : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SwapArithmetic_spec (X Y : Int) :
let (x, y) := SwapArithmetic X Y
x = Y ∧ y = X :=
sorry
-- </vc-theorems>