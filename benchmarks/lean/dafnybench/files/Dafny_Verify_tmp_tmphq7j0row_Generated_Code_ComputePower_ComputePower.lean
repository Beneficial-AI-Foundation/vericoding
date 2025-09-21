-- <vc-preamble>
def Power (n : Nat) : Nat :=
if n = 0 then 1 else 2 * Power (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ComputePower (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ComputePower_spec (n : Nat) :
ComputePower n = Power n :=
sorry
-- </vc-theorems>