import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def ComputeIsEven (x : Int) : Bool :=
if x % 2 = 0 then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeIsEven_spec (x : Int) :
ComputeIsEven x = (x % 2 = 0) :=
by simp [ComputeIsEven]
-- </vc-theorems>
