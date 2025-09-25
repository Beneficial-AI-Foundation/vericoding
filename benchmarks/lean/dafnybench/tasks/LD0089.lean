-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SwapSimultaneous (X Y : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SwapSimultaneous_spec (X Y : Int) :
let (x, y) := SwapSimultaneous X Y
x = Y ∧ y = X :=
sorry
-- </vc-theorems>