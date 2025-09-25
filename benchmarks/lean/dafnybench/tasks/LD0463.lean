-- <vc-preamble>
def distinct (nums : Array Int) : Prop :=
∀ i j, 0 ≤ i → i < j → j < nums.size → nums[i]! ≠ nums[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contains_duplicate (nums : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contains_duplicate_spec (nums : Array Int) :
(1 ≤ nums.size ∧ nums.size ≤ 100000) →
(∀ i, 0 ≤ i → i < nums.size → -1000000000 ≤ nums[i]! ∧ nums[i]! ≤ 1000000000) →
contains_duplicate nums = distinct nums :=
sorry
-- </vc-theorems>