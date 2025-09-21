-- <vc-preamble>
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  -- nums are sorted in non-decreasing order
  List.Pairwise (· ≤ ·) nums
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result

theorem removeDuplicates_spec_satisfied (nums: List Int) (h_precond : removeDuplicates_precond (nums)) :
    removeDuplicates_postcond (nums) (removeDuplicates (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>