/- 
-----Description-----
This task requires writing a Lean 4 method that finds the length of the logest common subsequence of two input arrays.

-----Input-----
The input consists of two arrays:
a: The first array.
b: The second array.

-----Output-----
The output is an integer:
Returns the length of array a and b's longest common subsequence.
-/

@[reducible]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

-- <vc-helpers>
def intMax (x y : Int) : Int :=
  if x < y then y else x
-- </vc-helpers>

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  sorry

@[reducible]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[1, 2, 3]"
        },
        "expected": 3,
        "unexpected": [
            2,
            4
        ]
    },
    {
        "input": {
            "a": "#[1, 3, 5, 7]",
            "b": "#[1, 2, 3, 4, 5, 6, 7]"
        },
        "expected": 4,
        "unexpected": [
            2,
            5
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5, 6]"
        },
        "expected": 0,
        "unexpected": [
            1,
            2
        ]
    },
    {
        "input": {
            "a": "#[]",
            "b": "#[1, 2, 3]"
        },
        "expected": 0,
        "unexpected": [
            1
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3, 4]",
            "b": "#[2, 4, 6, 8]"
        },
        "expected": 2,
        "unexpected": [
            1,
            3,
            4
        ]
    }
]
-/