-- <vc-preamble>
@[reducible]
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : List Int) (target : Int) (h_precond : twoSum_precond (nums) (target)) : Option (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        -- i must be the first i
        List.Pairwise (fun a b => a + b ≠ target) (nums.take i) ∧
        List.all (nums.take i) (fun a => List.all (nums.drop i) (fun b => a + b ≠ target) ) ∧
        -- j must be the first j
        List.all (nums.drop (j + 1)) (fun a => a + nums[j]! ≠ target)

theorem twoSum_spec_satisfied (nums: List Int) (target: Int) (h_precond : twoSum_precond (nums) (target)) :
    twoSum_postcond (nums) (target) (twoSum (nums) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>