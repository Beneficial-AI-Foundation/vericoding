-- <vc-preamble>
def Stairs (n : Nat) : Nat :=
if n ≤ 1 then 1 else Stairs (n - 2) + Stairs (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ClimbStairs (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ClimbStairs_spec (n : Nat) :
ClimbStairs n = Stairs n :=
sorry
-- </vc-theorems>