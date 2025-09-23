-- <vc-preamble>
@[reducible, simp]
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  let (i, j) := result
  -- two sum holds
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- i must be the first i
  List.Pairwise (fun a b => a + b ≠ target) (nums.toList.take i) ∧
  List.all (nums.toList.take i) (fun a => List.all (nums.toList.drop i) (fun b => a + b ≠ target) ) ∧
  -- j must be the first j
  List.all (nums.toList.drop (j + 1)) (fun a => a + nums[j]! ≠ target)

theorem twoSum_spec_satisfied (nums: Array Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>