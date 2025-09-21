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

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond nums target) : (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result : Nat × Nat) (h_precond : twoSum_precond nums target) : Prop :=
  let (i, j) := result
  0 ≤ i ∧ i < nums.size ∧
  0 ≤ j ∧ j < nums.size ∧
  i ≠ j ∧
  nums[i]! + nums[j]! = target

theorem twoSum_spec_satisfied (nums : Array Int) (target : Int) (h_precond : twoSum_precond nums target) :
    twoSum_postcond nums target (twoSum nums target h_precond) h_precond := by
  sorry
-- </vc-theorems>