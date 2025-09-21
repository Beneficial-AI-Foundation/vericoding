-- <vc-preamble>
@[reducible, simp]
def findMax_precond (nums : Array Int) : Prop :=
  nums.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findMax (nums : Array Int) (h_precond : findMax_precond nums) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findMax_postcond (nums : Array Int) (ret : Int) (h_precond : findMax_precond nums) : Prop :=
  (∀ i, i < nums.size → nums[i]! ≤ ret) ∧ (∃ i, i < nums.size ∧ nums[i]! = ret)

theorem findMax_spec_satisfied (nums : Array Int) (h_precond : findMax_precond nums) :
    findMax_postcond nums (findMax nums h_precond) h_precond := by
  sorry
-- </vc-theorems>