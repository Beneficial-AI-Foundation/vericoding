/- 
-----Description-----
This task involves concatenating two arrays of integers by appending the second array to the end of the first array. The goal is to produce a new array that sequentially contains all elements from the first array followed by all elements from the second array.

-----Input-----
The input consists of two parameters:
• a: An Array of integers representing the first part of the concatenated array.
• b: An Array of integers representing the second part of the concatenated array.

-----Output-----
The output is an Array of integers that satisfies the following:
• The length of the output array is equal to the sum of the lengths of arrays a and b.
• The first part of the output array (indices 0 to a.size - 1) is identical to array a.
• The remaining part of the output array (indices a.size to a.size + b.size - 1) is identical to array b.

-----Note-----
No additional preconditions are required since the function uses the sizes of the input arrays to build the resulting array.
-/

@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

theorem concat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : concat_precond (a) (b)) :
    concat_postcond (a) (b) (concat (a) (b) h_precond) h_precond := by
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
            "a": "#[1, 2, 3]",
            "b": "#[4, 5]"
        },
        "expected": "#[1, 2, 3, 4, 5]",
        "unexpected": [
            "#[1, 2, 3, 5, 4]",
            "#[4, 5, 1, 2, 3]",
            "#[1, 2, 4, 3, 5]"
        ]
    },
    {
        "input": {
            "a": "#[]",
            "b": "#[]"
        },
        "expected": "#[]",
        "unexpected": [
            "#[1]",
            "#[1, 2]"
        ]
    },
    {
        "input": {
            "a": "#[10]",
            "b": "#[20, 30, 40]"
        },
        "expected": "#[10, 20, 30, 40]",
        "unexpected": [
            "#[10, 20, 30]",
            "#[20, 30, 40, 10]"
        ]
    },
    {
        "input": {
            "a": "#[-1, -2]",
            "b": "#[0]"
        },
        "expected": "#[-1, -2, 0]",
        "unexpected": [
            "#[-1, 0, -2]",
            "#[0, -1, -2]"
        ]
    },
    {
        "input": {
            "a": "#[7, 8, 9]",
            "b": "#[]"
        },
        "expected": "#[7, 8, 9]",
        "unexpected": [
            "#[7, 8]",
            "#[8, 9]",
            "#[]"
        ]
    }
]
-/
