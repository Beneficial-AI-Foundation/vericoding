-- <vc-preamble>
def R (n : Nat) : Nat :=
if n = 0 then
0
else if R (n-1) > n then
R (n-1) - n
else
R (n-1) + n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calcR (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calcR_spec (n : Nat) : calcR n = R n :=
sorry
-- </vc-theorems>