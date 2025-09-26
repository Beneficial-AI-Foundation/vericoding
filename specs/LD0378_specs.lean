-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeElement (nums : Array Int) (val : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem removeElement_spec (nums : Array Int) (val : Int) (i : Nat) :
i < nums.size →
(∀ k, 0 < k ∧ k < i → nums[k]! ≠ val) :=
sorry
-- </vc-theorems>