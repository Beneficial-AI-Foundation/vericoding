/- 
-----Description-----
This task requires writing a Lean 4 function that computes the length of the longest strictly increasing contiguous subarray in a list of integers. A subarray is a sequence of consecutive elements, and it is strictly increasing if each element is greater than the previous one.

The function should correctly handle empty lists, lists with all equal elements, and long stretches of increasing numbers.

-----Input-----
The input consists of a single list:
nums: A list of integers.

-----Output-----
The output is a natural number:
Returns the length of the longest strictly increasing contiguous subarray. If the list is empty, the function should return 0.
-/

@[reducible]
def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[1, 2, 3, 2, 4, 5, 6]"
        },
        "expected": 4,
        "unexpected": [
            3,
            5
        ]
    },
    {
        "input": {
            "nums": "[10, 20, 30, 40]"
        },
        "expected": 4,
        "unexpected": [
            3
        ]
    },
    {
        "input": {
            "nums": "[5, 5, 5, 5]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "nums": "[10, 9, 8, 7]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "nums": "[]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 1, 2, 3, 0, 1, 2, 3, 4]"
        },
        "expected": 5,
        "unexpected": [
            4
        ]
    }
]
-/
