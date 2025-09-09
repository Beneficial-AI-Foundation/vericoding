import Mathlib.Data.List.Basic

@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

-- <vc-helpers>
def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0
-- </vc-helpers>

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  sorry

@[reducible]
def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem lengthOfLIS_spec_satisfied (nums: List Int) (h_precond : lengthOfLIS_precond (nums)) :
    lengthOfLIS_postcond (nums) (lengthOfLIS (nums) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "nums": "[10, 9, 2, 5, 3, 7, 101, 18]"
        },
        "expected": 4,
        "unexpected": [
            3,
            5,
            8
        ]
    },
    {
        "input": {
            "nums": "[0, 1, 0, 3, 2, 3]"
        },
        "expected": 4,
        "unexpected": [
            3,
            5
        ]
    },
    {
        "input": {
            "nums": "[7, 7, 7, 7, 7, 7, 7]"
        },
        "expected": 1,
        "unexpected": [
            0,
            7
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
            "nums": "[4, 10, 4, 3, 8, 9]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            6
        ]
    },
    {
        "input": {
            "nums": "[1, 3, 6, 7, 9, 4, 10, 5, 6]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            9
        ]
    },
    {
        "input": {
            "nums": "[10, 22, 9, 33, 21, 50, 41, 60, 80]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            9
        ]
    },
    {
        "input": {
            "nums": "[0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]"
        },
        "expected": 6,
        "unexpected": [
            5,
            7,
            16
        ]
    },
    {
        "input": {
            "nums": "[-2, -1]"
        },
        "expected": 2,
        "unexpected": [
            1,
            0
        ]
    }
]
-/