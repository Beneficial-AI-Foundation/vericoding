-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_element (nums : Array Int) (val : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_element_spec (nums : Array Int) (val : Int) :
(0 ≤ nums.size ∧ nums.size ≤ 100) →
(∀ i, 0 ≤ i ∧ i < nums.size → 0 ≤ nums[i]! ∧ nums[i]! ≤ 50) →
(0 ≤ val ∧ val ≤ 100) →
let i := remove_element nums val
∀ j:Nat, 0 < j ∧ j < i ∧ i < nums.size → nums[j]! ≠ val :=
sorry
-- </vc-theorems>