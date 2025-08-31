/- 
-----Description-----
This problem involves updating an array of integers by modifying two specific positions. Specifically, the element at index 4 should be increased by 3, and the element at index 7 should be changed to 516. The goal is to correctly update these positions while leaving the rest of the array unchanged. The description assumes that the array contains at least 8 elements.

-----Input-----
The input consists of:
• a: An array of integers. The array must contain at least 8 elements.

-----Output-----
The output is an array of integers that meets the following criteria:
• The element at index 4 is updated to its original value plus 3.
• The element at index 7 is set to 516.
• All other elements in the array remain the same as in the input array.

-----Note-----
It is assumed that the input array has a size of at least 8 elements. Indices are 0-indexed.
-/

@[reducible, simp]
def UpdateElements_precond (a : Array Int) : Prop :=
  a.size ≥ 8

-- <vc-helpers>
-- </vc-helpers>

def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def UpdateElements_postcond (a : Array Int) (result: Array Int) (h_precond : UpdateElements_precond (a)) :=
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

theorem UpdateElements_spec_satisfied (a: Array Int) (h_precond : UpdateElements_precond (a)) :
    UpdateElements_postcond (a) (UpdateElements (a) h_precond) h_precond := by
-- <vc-proof>
  sorry
-- </vc-proof>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "#[1, 2, 3, 4, 5, 6]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "#[0, 1, 2, 3, 4, 5, 6, 7, 8]"
        },
        "expected": "#[0, 1, 2, 3, 7, 5, 6, 516, 8]",
        "unexpected": [
            "#[0, 1, 2, 3, 4, 5, 6, 516, 8]",
            "#[0, 1, 2, 3, 7, 5, 6, 7, 8]"
        ]
    },
    {
        "input": {
            "a": "#[10, 20, 30, 40, 50, 60, 70, 80]"
        },
        "expected": "#[10, 20, 30, 40, 53, 60, 70, 516]",
        "unexpected": [
            "#[10, 20, 30, 40, 50, 60, 70, 80]",
            "#[10, 20, 30, 40, 53, 60, 70, 80]"
        ]
    },
    {
        "input": {
            "a": "#[-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]"
        },
        "expected": "#[-1, -2, -3, -4, -2, -6, -7, 516, -9, -10]",
        "unexpected": [
            "#[-1, -2, -3, -4, -5, -6, -7, 516, -9, -10]",
            "#[-1, -2, -3, -4, -2, -6, -7, -8, -9, -10]"
        ]
    },
    {
        "input": {
            "a": "#[0, 0, 0, 0, 0, 0, 0, 0]"
        },
        "expected": "#[0, 0, 0, 0, 3, 0, 0, 516]",
        "unexpected": [
            "#[0, 0, 0, 0, 0, 0, 0, 516]",
            "#[0, 0, 0, 0, 3, 0, 0, 0]"
        ]
    },
    {
        "input": {
            "a": "#[5, 5, 5, 5, 5, 5, 5, 5]"
        },
        "expected": "#[5, 5, 5, 5, 8, 5, 5, 516]",
        "unexpected": [
            "#[5, 5, 5, 5, 5, 5, 5, 5]",
            "#[5, 5, 5, 5, 8, 5, 5, 5]"
        ]
    }
]
-/