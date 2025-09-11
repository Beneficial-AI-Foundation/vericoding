-- <vc-preamble>
import Mathlib.Data.List.Basic

@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>

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
            100
        ]
    },
    {
        "input": {
            "nums": "[0, 1, 0, 3, 2, 3]"
        },
        "expected": 4,
        "unexpected": [
            3,
            100
        ]
    },
    {
        "input": {
            "nums": "[7, 7, 7, 7, 7, 7, 7]"
        },
        "expected": 1,
        "unexpected": [
            7,
            7
        ]
    },
    {
        "input": {
            "nums": "[1, 3, 2, 4]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4
        ]
    },
    {
        "input": {
            "nums": "[10]"
        },
        "expected": 1,
        "unexpected": [
            0
        ]
    }
]
-/