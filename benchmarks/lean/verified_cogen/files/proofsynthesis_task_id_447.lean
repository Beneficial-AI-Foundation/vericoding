-- <vc-preamble>
@[reducible, simp]
def cubeElement_precond (nums : Array Int) :=
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! ≤ 2147483647) ∧
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! * nums[k]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cubeElement (nums : Array Int) (h_precond : cubeElement_precond (nums)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeElement_postcond (nums : Array Int) (cubed: Array Int) (h_precond : cubeElement_precond (nums)) :=
  ∀ i, i < nums.size → cubed[i]! = nums[i]! * nums[i]! * nums[i]!

theorem cubeElement_spec_satisfied (nums: Array Int) (h_precond : cubeElement_precond (nums)) :
    cubeElement_postcond (nums) (cubeElement (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>