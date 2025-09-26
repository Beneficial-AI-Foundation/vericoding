import Mathlib
-- <vc-preamble>
def power (x : Float) (n : Nat) : Float :=
if n = 0 then 1.0 else x * power x (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def powerDC (x : Float) (n : Nat) : Float :=
power x n
-- </vc-definitions>

-- <vc-theorems>
theorem powerDC_spec (x : Float) (n : Nat) :
powerDC x n = power x n :=
rfl
-- </vc-theorems>
