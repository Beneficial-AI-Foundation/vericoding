-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveDuplicates (nums : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveDuplicates_spec (nums : Array Int) (num_length : Int) :
(∀ i j, 0 ≤ i ∧ i < j ∧ j < nums.size → nums[i]! ≤ nums[j]!) →
(num_length = RemoveDuplicates nums) →
(0 ≤ num_length ∧ num_length ≤ nums.size) ∧
(∀ i j:Nat, 0 ≤ i ∧ i < j ∧ j < num_length → nums[i]! ≠ nums[j]!) :=
sorry
-- </vc-theorems>