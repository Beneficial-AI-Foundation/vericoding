import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def SwapBitvectors (X Y : UInt8) : UInt8 × UInt8 :=
(Y, X)
-- </vc-definitions>

-- <vc-theorems>
theorem SwapBitvectors_spec (X Y : UInt8) :
let (x, y) := SwapBitvectors X Y
x = Y ∧ y = X :=
And.intro rfl rfl
-- </vc-theorems>
