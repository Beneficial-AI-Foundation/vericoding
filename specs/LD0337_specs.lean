-- <vc-preamble>
def power (x : Float) (n : Nat) : Float :=
if n = 0 then 1.0 else x * power x (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def powerIter (b : Float) (n : Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem powerIter_spec (b : Float) (n : Nat) :
powerIter b n = power b n :=
sorry
-- </vc-theorems>