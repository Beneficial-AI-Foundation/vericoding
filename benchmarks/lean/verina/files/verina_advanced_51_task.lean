-- <vc-preamble>
@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

theorem mergeSorted_spec_satisfied (a: List Int) (b: List Int) (h_precond : mergeSorted_precond (a) (b)) :
    mergeSorted_postcond (a) (b) (mergeSorted (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[
    {
        "input": {
            "a": "[1, 2, 3]",
            "b": "[6, 5, 4]"
        }
    },
    {
        "input": {
            "a": "[3, 2, 1]",
            "b": "[6, 5, 4]"
        }
    }
]
-- Tests
[
    {
        "input": {
            "a": "[1, 3, 5]",
            "b": "[2, 4, 6]"
        },
        "expected": "[1, 2, 3, 4, 5, 6]",
        "unexpected": [
            "[1, 3, 5]",
            "[2, 4, 6]",
            "[6, 5, 4]"
        ]
    },
    {
        "input": {
            "a": "[1, 2]",
            "b": "[1, 2, 3]"
        },
        "expected": "[1, 1, 2, 2, 3]",
        "unexpected": [
            "[1, 2, 3]"
        ]
    },
    {
        "input": {
            "a": "[]",
            "b": "[4, 5]"
        },
        "expected": "[4, 5]",
        "unexpected": [
            "[]"
        ]
    },
    {
        "input": {
            "a": "[0, 3, 4]",
            "b": "[]"
        },
        "expected": "[0, 3, 4]",
        "unexpected": [
            "[4, 3, 0]"
        ]
    },
    {
        "input": {
            "a": "[1, 4, 6]",
            "b": "[2, 3, 5]"
        },
        "expected": "[1, 2, 3, 4, 5, 6]",
        "unexpected": [
            "[1, 4, 6, 2, 3, 5]"
        ]
    }
]
-/