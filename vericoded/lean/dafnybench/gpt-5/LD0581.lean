import Mathlib
-- <vc-preamble>
partial def verifyNeg (a : Array Int) (idx : Int) : Nat :=
if idx == 0 then 0
else verifyNeg a (idx - 1) + (if a[(idx - 1).toNat]! < 0 then 1 else 0)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers required for this file
-- </vc-helpers>

-- <vc-definitions>
def CountNeg (a : Array Int) : Nat :=
verifyNeg a a.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountNeg_spec (a : Array Int) :
CountNeg a = verifyNeg a a.size :=
rfl
-- </vc-theorems>
