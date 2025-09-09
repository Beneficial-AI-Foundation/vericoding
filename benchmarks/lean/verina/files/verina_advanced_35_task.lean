import Std.Data.HashMap
open Std

@[reducible]
def majorityElement_precond (nums : List Int) : Prop :=
  nums.length > 0 ∧ nums.any (fun x => nums.count x > nums.length / 2)

-- <vc-helpers>
-- </vc-helpers>

def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  sorry

@[reducible]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  let n := nums.length
  (nums.count result) > n / 2
  ∧ ∀ x, x ≠ result → nums.count x ≤ n / 2

theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[1, 2, 3]"
        }
    },
    {
        "input": {
            "nums": "[]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[3, 2, 3]"
        },
        "expected": 3,
        "unexpected": [
            2
        ]
    },
    {
        "input": {
            "nums": "[2, 2, 1, 1, 1, 2, 2]"
        },
        "expected": 2,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[1, 1, 1, 2, 3, 1]"
        },
        "expected": 1,
        "unexpected": [
            2,
            3
        ]
    },
    {
        "input": {
            "nums": "[0, 0, 0, 0]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "nums": "[7]"
        },
        "expected": 7,
        "unexpected": []
    }
]
-/