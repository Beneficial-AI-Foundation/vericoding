import Mathlib
-- <vc-preamble>
def Stairs (n : Nat) : Nat :=
if n ≤ 1 then 1 else Stairs (n - 2) + Stairs (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Nat

-- </vc-helpers>

-- <vc-definitions>
def ClimbStairs (n : Nat) : Nat :=
Stairs n
-- </vc-definitions>

-- <vc-theorems>
theorem ClimbStairs_spec (n : Nat) :
ClimbStairs n = Stairs n :=
by rfl
-- </vc-theorems>
