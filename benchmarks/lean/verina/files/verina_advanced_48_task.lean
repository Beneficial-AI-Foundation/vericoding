-- <vc-preamble>
@[reducible, simp]
def mergeSort_precond (list : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSort (list : List Int) (h_precond : mergeSort_precond (list)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mergeSort_postcond (list : List Int) (result: List Int) (h_precond : mergeSort_precond (list)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm list result

theorem mergeSort_spec_satisfied (list: List Int) (h_precond : mergeSort_precond (list)) :
    mergeSort_postcond (list) (mergeSort (list) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "list": "[5, 2, 9, 1, 5, 6]"
        },
        "expected": "[1, 2, 5, 5, 6, 9]",
        "unexpected": [
            "[5, 2, 9, 1, 5, 6]",
            "[9, 6, 5, 5, 2, 1]"
        ]
    },
    {
        "input": {
            "list": "[3, 1, 4, 1, 5, 9, 2, 6]"
        },
        "expected": "[1, 1, 2, 3, 4, 5, 6, 9]",
        "unexpected": [
            "[3, 1, 4, 1, 5, 9, 2, 6]",
            "[9, 6, 5, 4, 3, 2, 1, 1]"
        ]
    },
    {
        "input": {
            "list": "[]"
        },
        "expected": "[]",
        "unexpected": [
            "[1]"
        ]
    },
    {
        "input": {
            "list": "[1]"
        },
        "expected": "[1]",
        "unexpected": [
            "[]"
        ]
    },
    {
        "input": {
            "list": "[5, 5, 5, 5]"
        },
        "expected": "[5, 5, 5, 5]",
        "unexpected": [
            "[5, 5, 5]",
            "[5, 5, 5, 5, 5]"
        ]
    },
    {
        "input": {
            "list": "[9, 8, 7, 6, 5, 4, 3, 2, 1]"
        },
        "expected": "[1, 2, 3, 4, 5, 6, 7, 8, 9]",
        "unexpected": [
            "[9, 8, 7, 6, 5, 4, 3, 2, 1]"
        ]
    },
    {
        "input": {
            "list": "[1, 2, 3, 4, 5]"
        },
        "expected": "[1, 2, 3, 4, 5]",
        "unexpected": [
            "[5, 4, 3, 2, 1]"
        ]
    },
    {
        "input": {
            "list": "[-3, -1, -5, -2]"
        },
        "expected": "[-5, -3, -2, -1]",
        "unexpected": [
            "[-3, -1, -5, -2]",
            "[-1, -2, -3, -5]"
        ]
    }
]
-/