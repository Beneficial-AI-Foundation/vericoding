-- <vc-preamble>
def power (x : Float) (n : Nat) : Float :=
if n = 0 then 1.0 else x * power x (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerDC (x : Float) (n : Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powerDC_spec (x : Float) (n : Nat) :
powerDC x n = power x n :=
sorry
-- </vc-theorems>