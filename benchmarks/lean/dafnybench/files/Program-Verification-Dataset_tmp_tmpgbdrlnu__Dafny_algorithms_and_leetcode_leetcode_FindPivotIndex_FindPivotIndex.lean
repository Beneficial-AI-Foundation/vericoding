-- <vc-preamble>
partial def sum (nums : Array Int) : Int :=
if nums.size = 0 then 0
else sum (nums.extract 0 (nums.size - 1)) + nums[nums.size - 1]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindPivotIndex (nums : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindPivotIndex_spec (nums : Array Int) :
nums.size > 0 →
(let index := FindPivotIndex nums
(index = -1 →
∀ k : Nat, k < nums.size →
sum (nums.extract 0 k) ≠ sum (nums.extract (k+1) nums.size)) ∧
(0 ≤ index ∧ index < nums.size →
sum (nums.extract 0 index.toNat) = sum (nums.extract (index.toNat+1) nums.size))) :=
sorry
-- </vc-theorems>