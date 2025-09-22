-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CalcPower (n : Nat) : Nat :=
sorry

def ComputePower (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CalcPower_spec (n : Nat) : CalcPower n = 2*n :=
sorry

theorem ComputePower_spec (n : Nat) : ComputePower n = Power n :=
sorry
-- </vc-theorems>