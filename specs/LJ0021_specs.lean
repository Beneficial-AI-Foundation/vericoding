-- <vc-preamble>
@[reducible, simp]
def linearSearch_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size < 0x80000000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def linearSearch (nums : Array Int) (target : Int) (h_precond : linearSearch_precond nums target) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def linearSearch_postcond (nums : Array Int) (target : Int) (ret : Int) (h_precond : linearSearch_precond nums target) : Prop :=
  ret < nums.size ∧ 
  (ret ≥ 0 → nums[ret.natAbs]! = target) ∧
  (ret ≥ 0 → ∀ i : Int, 0 ≤ i ∧ i < ret → nums[i.natAbs]! ≠ target) ∧
  (ret < 0 → ∀ i : Int, 0 ≤ i ∧ i < nums.size → nums[i.natAbs]! ≠ target)

theorem linearSearch_spec_satisfied (nums : Array Int) (target : Int) (h_precond : linearSearch_precond nums target) :
    linearSearch_postcond nums target (linearSearch nums target h_precond) h_precond := by
  sorry
-- </vc-theorems>