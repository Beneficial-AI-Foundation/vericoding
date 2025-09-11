-- <vc-preamble>
@[reducible, simp]
def uniqueSorted_precond (arr : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def uniqueSorted_postcond (arr : List Int) (result: List Int) (h_precond : uniqueSorted_precond (arr)) : Prop :=
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result

theorem uniqueSorted_spec_satisfied (arr: List Int) (h_precond : uniqueSorted_precond (arr)) :
    uniqueSorted_postcond (arr) (uniqueSorted (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "arr": "[1, 1, 2, 3]"
        },
        "expected": "[1, 2, 3]",
        "unexpected": [
            "[1, 1, 2, 3]",
            "[2, 3, 1]",
            "[1, 3, 2]"
        ]
    },
    {
        "input": {
            "arr": "[3, 3, 3]"
        },
        "expected": "[3]",
        "unexpected": [
            "[3, 3, 3]",
            "[3, 3]",
            "[3, 3, 3, 3]"
        ]
    },
    {
        "input": {
            "arr": "[]"
        },
        "expected": "[]",
        "unexpected": [
            "[0]",
            "[1]",
            "[999]"
        ]
    },
    {
        "input": {
            "arr": "[5, 2, 2, 5]"
        },
        "expected": "[2, 5]",
        "unexpected": [
            "[5, 2]",
            "[2, 2, 5]",
            "[2]"
        ]
    },
    {
        "input": {
            "arr": "[1, 2, 3, 4, 5]"
        },
        "expected": "[1, 2, 3, 4, 5]",
        "unexpected": [
            "[1, 2, 3]",
            "[2, 3, 4, 5]",
            "[5, 4, 3, 2, 1]"
        ]
    }
]
-/