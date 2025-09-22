-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Swap (X Y : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Swap_spec (X Y : Int) :
let (x, y) := Swap X Y
x = Y ∧ y = X :=
sorry
-- </vc-theorems>