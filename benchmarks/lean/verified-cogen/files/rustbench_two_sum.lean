-- <vc-preamble>
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size ≥ 2 ∧ 
  (∃ i j, 0 ≤ i ∧ i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target) ∧
  (∀ i j, 0 ≤ i ∧ i < nums.size ∧ 0 ≤ j ∧ j < nums.size → 
    nums[i]! + nums[j]! ≤ 2147483647 ∧ nums[i]! + nums[j]! ≥ -2147483648)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()