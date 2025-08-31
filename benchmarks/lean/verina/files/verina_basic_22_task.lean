/- 
-----Description-----
This task requires writing a Lean 4 method that identifies the dissimilar elements between two arrays of integers. In other words, the method should return an array containing all elements that appear in one input array but not in the other. The output array must contain no duplicate elements and the order of elements does not matter.

-----Input-----
The input consists of:
a: An array of integers.
b: An array of integers.

-----Output-----
The output is an array of integers:
Returns an array containing all distinct elements from both input arrays that are not present in the other array and should be sorted
-/

import Std.Data.HashSet

@[reducible, simp]
def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  True

-- <vc-helpers>
def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)
-- </vc-helpers>

def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def dissimilarElements_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :=
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)

theorem dissimilarElements_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    dissimilarElements_postcond (a) (b) (dissimilarElements (a) (b) h_precond) h_precond := by
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
            "a": "#[1, 2, 3, 4]",
            "b": "#[3, 4, 5, 6]"
        },
        "expected": "#[1, 2, 5, 6]",
        "unexpected": [
            "#[1,2,3,4,5,6]",
            "#[3,4]",
            "#[1,3,5]"
        ]
    },
    {
        "input": {
            "a": "#[1, 1, 2]",
            "b": "#[2, 3]"
        },
        "expected": "#[1, 3]",
        "unexpected": [
            "#[1]",
            "#[3]",
            "#[1,2,3]"
        ]
    },
    {
        "input": {
            "a": "#[]",
            "b": "#[4, 5]"
        },
        "expected": "#[4, 5]",
        "unexpected": [
            "#[4]",
            "#[5]",
            "#[]"
        ]
    },
    {
        "input": {
            "a": "#[7, 8]",
            "b": "#[]"
        },
        "expected": "#[7, 8]",
        "unexpected": [
            "#[7]",
            "#[8]",
            "#[7, 8, 9]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[1, 2, 3]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[1,2]",
            "#[1,2,3]"
        ]
    },
    {
        "input": {
            "a": "#[1, 2, 3]",
            "b": "#[4, 5, 6]"
        },
        "expected": "#[1, 2, 3, 4, 5, 6]",
        "unexpected": [
            "#[1,2,3,4]",
            "#[4,5,6]",
            "#[1,2,3]"
        ]
    },
    {
        "input": {
            "a": "#[-1, 0, 1]",
            "b": "#[0]"
        },
        "expected": "#[-1, 1]",
        "unexpected": [
            "#[0]",
            "#[-1,0,1]",
            "#[-1]"
        ]
    }
]
-/