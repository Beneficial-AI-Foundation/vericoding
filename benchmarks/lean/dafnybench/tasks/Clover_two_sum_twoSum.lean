-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem twoSum_spec (nums : Array Int) (target : Int) :
nums.size > 1 →
(∃ i j, 0 ≤ i ∧ i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target) →
let (i, j) := twoSum nums target
0 ≤ i ∧ i < j ∧ j < nums.size ∧ nums[i.toNat]! + nums[j.toNat]! = target ∧
(∀ ii jj, 0 ≤ ii ∧ ii < i ∧ ii < jj ∧ jj < nums.size → nums[ii.toNat]! + nums[jj.toNat]! ≠ target) ∧
(∀ jj, i < jj ∧ jj < j → nums[i.toNat]! + nums[jj.toNat]! ≠ target) :=
sorry
-- </vc-theorems>