-- <vc-preamble>
@[reducible, simp]
def maxArray_precond (nums : Array Int) := 
  nums.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxArray (nums : Array Int) (h_precond : maxArray_precond nums) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxArray_postcond (nums : Array Int) (idx : Nat) (h_precond : maxArray_precond nums) :=
  0 ≤ idx ∧ idx < nums.size ∧ (∀ i, i < nums.size → nums[i]! ≤ nums[idx]!)

theorem maxArray_spec_satisfied (nums : Array Int) (h_precond : maxArray_precond nums) :
    maxArray_postcond nums (maxArray nums h_precond) h_precond := by
  sorry
-- </vc-theorems>