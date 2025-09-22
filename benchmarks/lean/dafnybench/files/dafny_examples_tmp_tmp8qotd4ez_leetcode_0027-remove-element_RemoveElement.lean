-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveElement (nums : Array Int) (val : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveElement_spec (nums : Array Int) (val : Int) :
let newLength := RemoveElement nums val
0 ≤ newLength ∧ newLength ≤ nums.size :=
sorry
-- </vc-theorems>