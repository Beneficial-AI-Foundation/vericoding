import Mathlib
-- <vc-preamble>
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  -- nums are sorted in non-decreasing order
  List.Pairwise (· ≤ ·) nums
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers are required for this verification.
-- </vc-helpers>

-- <vc-definitions>
def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  nums.eraseDups.length
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result

theorem removeDuplicates_spec_satisfied (nums: List Int) (h_precond : removeDuplicates_precond (nums)) :
    removeDuplicates_postcond (nums) (removeDuplicates (nums) h_precond) h_precond := by
  dsimp [removeDuplicates_postcond, removeDuplicates]
  constructor
  · simp
  · exact le_rfl
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "nums": "[3, 2, 1]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "nums": "[1, 1, 2]"
        },
        "expected": 2,
        "unexpected": [
            1,
            3
        ]
    },
    {
        "input": {
            "nums": "[0, 0, 1, 1, 1, 2, 2, 3, 3, 4]"
        },
        "expected": 5,
        "unexpected": [
            4,
            10
        ]
    },
    {
        "input": {
            "nums": "[-1, -1, 0, 1, 2, 2, 3]"
        },
        "expected": 5,
        "unexpected": [
            3
        ]
    },
    {
        "input": {
            "nums": "[1, 2, 3, 4, 5]"
        },
        "expected": 5,
        "unexpected": [
            4
        ]
    },
    {
        "input": {
            "nums": "[1, 1, 1, 1]"
        },
        "expected": 1,
        "unexpected": [
            2,
            4
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
            "nums": "[1]"
        },
        "expected": 1,
        "unexpected": [
            0,
            2
        ]
    },
    {
        "input": {
            "nums": "[-100, -100, -100]"
        },
        "expected": 1,
        "unexpected": [
            2,
            3
        ]
    },
    {
        "input": {
            "nums": "[-100, -99, -99, -50, 0, 0, 100, 100]"
        },
        "expected": 5,
        "unexpected": [
            6,
            7
        ]
    },
    {
        "input": {
            "nums": "[-1, 0, 0, 0, 1, 2, 2, 3, 4, 4, 5]"
        },
        "expected": 7,
        "unexpected": [
            6,
            10
        ]
    },
    {
        "input": {
            "nums": "[100, 100, 100, 101, 102, 102, 103, 104, 105, 105]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7
        ]
    }
]
-/