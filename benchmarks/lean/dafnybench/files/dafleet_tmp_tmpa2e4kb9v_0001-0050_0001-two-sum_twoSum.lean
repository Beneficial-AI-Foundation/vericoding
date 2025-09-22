-- <vc-preamble>
def correct_pair (pair : Int × Int) (nums : Array Int) (target : Int) : Prop :=
let (i, j) := pair
0 ≤ i ∧ i < nums.size ∧
0 ≤ j ∧ j < nums.size ∧
i ≠ j ∧
nums[i.toNat]! + nums[j.toNat]! = target
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem twoSum_spec (nums : Array Int) (target : Int) :
(∃ i j, correct_pair (i, j) nums target) →
correct_pair (twoSum nums target) nums target :=
sorry
-- </vc-theorems>