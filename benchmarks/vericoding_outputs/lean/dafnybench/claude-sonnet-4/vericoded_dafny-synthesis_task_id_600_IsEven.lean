import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def IsEven (n : Int) : Bool :=
if n % 2 = 0 then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem IsEven_spec (n : Int) :
IsEven n = (n % 2 = 0) :=
by simp [IsEven]
-- </vc-theorems>
