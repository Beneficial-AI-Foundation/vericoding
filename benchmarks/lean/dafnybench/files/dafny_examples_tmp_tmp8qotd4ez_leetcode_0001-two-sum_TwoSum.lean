-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def TwoSum (nums : Array Int) (target : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem TwoSum_spec (nums : Array Int) (target : Int) :
let r := TwoSum nums target
(0 ≤ r.1 →
(0 ≤ r.1 ∧ r.1 < r.2 ∧ r.2 < nums.size ∧
nums[r.1.toNat]! + nums[r.2.toNat]! = target ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < r.2 → nums[i.toNat]! + nums[j.toNat]! ≠ target))) ∧
(r.1 = -1 ↔
(∀ i j, 0 ≤ i ∧ i < j ∧ j < nums.size → nums[i]! + nums[j]! ≠ target)) :=
sorry
-- </vc-theorems>