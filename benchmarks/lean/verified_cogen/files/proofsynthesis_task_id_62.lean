-- <vc-preamble>
@[reducible, simp]
def smallestNum_precond (nums : Array Int) :=
  nums.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestNum (nums : Array Int) (h_precond : smallestNum_precond nums) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def smallestNum_postcond (nums : Array Int) (min : Int) (h_precond : smallestNum_precond nums) :=
  (∀ i, i < nums.size → min ≤ nums[i]!) ∧ (∃ i, i < nums.size ∧ min = nums[i]!)

theorem smallestNum_spec_satisfied (nums : Array Int) (h_precond : smallestNum_precond nums) :
    smallestNum_postcond nums (smallestNum nums h_precond) h_precond := by
  sorry
-- </vc-theorems>