import Mathlib
-- <vc-preamble>
@[reducible, simp]
def squareNums_precond (nums : Array Int) : Prop :=
  ∀ k, 0 ≤ k ∧ k < nums.size → 0 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! < 2147483647
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def squareNums (nums : Array Int) (h_precond : squareNums_precond (nums)) : Array Int :=
  nums.map (fun x => x * x)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def squareNums_postcond (nums : Array Int) (squared: Array Int) (h_precond : squareNums_precond (nums)) : Prop :=
  nums.size = squared.size ∧ (∀ k, 0 ≤ k ∧ k < nums.size → squared[k]! = nums[k]! * nums[k]!)

theorem squareNums_spec_satisfied (nums: Array Int) (h_precond : squareNums_precond (nums)) :
    squareNums_postcond (nums) (squareNums (nums) h_precond) h_precond := by
  unfold squareNums_postcond
  constructor
  · simp [squareNums]
  · intro k hk
    have hk' : k < nums.size := hk.2
    have hkmap : k < (nums.map (fun x => x * x)).size := by simpa using hk'
    simpa [squareNums, Array.get!, hk', hkmap]
-- </vc-theorems>
