-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SplitArray (arr : Array Int) (L : Int) : Array Int × Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SplitArray_spec (arr : Array Int) (L : Int) :
(0 ≤ L ∧ L ≤ arr.size) →
let (firstPart, secondPart) := SplitArray arr L
firstPart.size = L ∧
secondPart.size = arr.size - L ∧
(firstPart.append secondPart) = arr :=
sorry
-- </vc-theorems>