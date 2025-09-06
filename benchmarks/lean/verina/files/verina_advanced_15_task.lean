/- 
-----Description-----
Given an integer array nums, return true if there exists a triple of indices (i, j, k) such that i < j < k and nums[i] < nums[j] < nums[k]. If no such indices exist, return false.

-----Input-----
The input consists of a single list:
nums: A list of integers.

-----Output-----
The output is a boolean:
Returns true if there exists a triplet (i, j, k) where i < j < k and nums[i] < nums[j] < nums[k]; otherwise, returns false.
-/

@[reducible]
def increasingTriplet_precond (nums : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def increasingTriplet (nums : List Int) (h_precond : increasingTriplet_precond (nums)) : Bool :=
  sorry

@[reducible]
def increasingTriplet_postcond (nums : List Int) (result: Bool) (h_precond : increasingTriplet_precond (nums)) : Prop :=
  let nums' := nums.zipIdx
  (result →
    nums'.any (fun (x, i) =>
      nums'.any (fun (y, j) =>
        nums'.any (fun (z, k) =>
          i < j ∧ j < k ∧ x < y ∧ y < z
        )
      )
    ))
  ∧
  (¬ result → nums'.all (fun (x, i) =>
    nums'.all (fun (y, j) =>
      nums'.all (fun (z, k) =>
        i ≥ j ∨ j ≥ k ∨ x ≥ y ∨ y ≥ z
      )
    )
  ))

theorem increasingTriplet_spec_satisfied (nums: List Int) (h_precond : increasingTriplet_precond (nums)) :
    increasingTriplet_postcond (nums) (increasingTriplet (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[1, 2, 3]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "nums": "[5, 4, 3, 2, 1]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "nums": "[2, 1, 5, 0, 4, 6]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "nums": "[1, 5, 0, 4, 1, 3]"
        },
        "expected": true,
        "unexpected": [
            false
        ]
    },
    {
        "input": {
            "nums": "[5, 4, 3]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    },
    {
        "input": {
            "nums": "[]"
        },
        "expected": false,
        "unexpected": [
            true
        ]
    }
]
-/