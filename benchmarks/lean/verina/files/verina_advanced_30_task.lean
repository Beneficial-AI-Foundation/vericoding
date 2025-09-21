-- <vc-preamble>
@[reducible]
def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestIncreasingStreak_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingStreak_precond (nums)) : Prop :=
  -- Case 1: Empty list means result = 0
  (nums = [] → result = 0) ∧

  -- Case 2: If result > 0, there exists a streak of exactly that length
  (result > 0 →
    (List.range (nums.length - result + 1) |>.any (fun start =>
      -- Check bounds are valid
      start + result ≤ nums.length ∧
      -- Check all consecutive pairs in this streak are increasing
      (List.range (result - 1) |>.all (fun i =>
        nums[start + i]! < nums[start + i + 1]!)) ∧
      -- Check this streak can't be extended left (if possible)
      (start = 0 ∨ nums[start - 1]! ≥ nums[start]!) ∧
      -- Check this streak can't be extended right (if possible)
      (start + result = nums.length ∨ nums[start + result - 1]! ≥ nums[start + result]!)))) ∧

  -- Case 3: No streak longer than result exists
  (List.range (nums.length - result) |>.all (fun start =>
    List.range result |>.any (fun i =>
      start + i + 1 ≥ nums.length ∨ nums[start + i]! ≥ nums[start + i + 1]!)))

theorem longestIncreasingStreak_spec_satisfied (nums: List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    longestIncreasingStreak_postcond (nums) (longestIncreasingStreak (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>