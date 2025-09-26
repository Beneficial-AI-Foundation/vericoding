import Mathlib
-- <vc-preamble>
partial def sum (n : Nat) : Nat :=
if n == 0 then 0
else n + sum (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def sumBackwards (n : Nat) : Nat :=
sum n
-- </vc-definitions>

-- <vc-theorems>
theorem sumBackwards_spec (n : Nat) :
sumBackwards n = sum n :=
rfl
-- </vc-theorems>
