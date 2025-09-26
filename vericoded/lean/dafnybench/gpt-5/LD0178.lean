import Mathlib
-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def CalcPower (n : Nat) : Nat :=
2 * n

def ComputePower (n : Nat) : Nat :=
Power n
-- </vc-definitions>

-- <vc-theorems>
theorem CalcPower_spec (n : Nat) : CalcPower n = 2*n :=
rfl

theorem ComputePower_spec (n : Nat) : ComputePower n = Power n :=
rfl
-- </vc-theorems>
