import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this simple swap function

-- </vc-helpers>

-- <vc-definitions>
def SwapBitvectors (X Y : UInt8) : UInt8 × UInt8 :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapBitvectors_spec (X Y : UInt8) :
let (x, y) := SwapBitvectors X Y
x = Y ∧ y = X :=
by
dsimp [SwapBitvectors]
constructor
rfl
rfl
-- </vc-theorems>
