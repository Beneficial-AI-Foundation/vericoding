import Mathlib
-- <vc-preamble>
def sumNegativesTo (a : Array Int) (n : Nat) : Int :=
if n = 0 then 0
else if (a[n-1]!) < 0 then
sumNegativesTo a (n-1) + (a[n-1]!)
else
sumNegativesTo a (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for proving properties about sumNegativesTo
lemma sumNegativesTo_zero (a : Array Int) : sumNegativesTo a 0 = 0 := by
  simp [sumNegativesTo]
-- </vc-helpers>

-- <vc-definitions>
def SumOfNegatives (a : Array Int) : Int :=
sumNegativesTo a a.size
-- </vc-definitions>

-- <vc-theorems>
theorem SumOfNegatives_spec (a : Array Int) :
SumOfNegatives a = sumNegativesTo a a.size :=
rfl
-- </vc-theorems>
