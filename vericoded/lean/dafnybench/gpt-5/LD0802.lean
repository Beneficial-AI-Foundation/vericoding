import Mathlib
-- <vc-preamble>
def sumTo (a : Array Int) (n : Nat) : Int :=
if n = 0 then 0
else sumTo a (n-1) + a[n-1]!
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this file.
-- </vc-helpers>

-- <vc-definitions>
def ArraySum (a : Array Int) : Int :=
sumTo a a.size
-- </vc-definitions>

-- <vc-theorems>
theorem ArraySum_spec (a : Array Int) :
ArraySum a = sumTo a a.size :=
rfl
-- </vc-theorems>
