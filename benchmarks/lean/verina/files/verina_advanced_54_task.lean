/- 
-----Description-----
This task requires writing a Lean 4 function that finds the one missing number in a list of distinct natural numbers from 0 to n. The list contains exactly n numbers and all numbers are in the range [0, n], but one number in that range is missing.

Your function must return the missing number. You may assume the input list contains no duplicates and only one number is missing.

-----Input-----
- nums: A list of natural numbers of length n, each in the range [0, n] with exactly one number missing.

-----Output-----
- A natural number: the missing number in the range [0, n] not present in the list.
-/

@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums

-- <vc-helpers>
-- </vc-helpers>

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  sorry

@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums

theorem missingNumber_spec_satisfied (nums: List Nat) (h_precond : missingNumber_precond (nums)) :
    missingNumber_postcond (nums) (missingNumber (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[0, 0, 1]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[3, 0, 1]"
        },
        "expected": 2,
        "unexpected": [
            0,
            1,
            3
        ]
    },
    {
        "input": {
            "nums": "[0, 1]"
        },
        "expected": 2,
        "unexpected": [
            0,
            1
        ]
    },
    {
        "input": {
            "nums": "[9, 6, 4, 2, 3, 5, 7, 0, 1]"
        },
        "expected": 8,
        "unexpected": [
            1,
            9
        ]
    },
    {
        "input": {
            "nums": "[0]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    },
    {
        "input": {
            "nums": "[1]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    }
]
-/