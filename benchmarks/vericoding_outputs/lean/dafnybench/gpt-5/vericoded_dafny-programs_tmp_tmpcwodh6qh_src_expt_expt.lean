import Mathlib
-- <vc-preamble>
partial def Expt (b : Int) (n : Nat) : Int :=
if n == 0 then 1 else b * Expt b (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def expt (b : Int) (n : Nat) : Int :=
Expt b n
-- </vc-definitions>

-- <vc-theorems>
theorem expt_spec (b : Int) (n : Nat) :
expt b n = Expt b n :=
rfl
-- </vc-theorems>
