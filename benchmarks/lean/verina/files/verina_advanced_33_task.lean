import Mathlib.Data.List.Basic

@[reducible, simp]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  sorry

@[reducible, simp]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
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
            5
        ]
    },
    {
        "input": {
            "nums": "[0, 1, 0, 3, 2, 3]"
        },
        "expected": 4,
        "unexpected": [
            3
        ]
    },
    {
        "input": {
            "nums": "[7, 7, 7, 7, 7]"
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
            "nums": "[4, 10, 4, 3, 8, 9]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4
        ]
    }
]
-/