import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def IsEven (n : Int) : Bool :=
n % 2 == 0
-- </vc-definitions>

-- <vc-theorems>
theorem IsEven_spec (n : Int) :
IsEven n = (n % 2 = 0) :=
by simp [IsEven]
-- </vc-theorems>
