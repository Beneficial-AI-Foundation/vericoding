/- 
-----Description-----
This task involves creating a function that swaps two integer values. Given two integers, the function should return a pair where the first element is the second input value and the second element is the first input value.

-----Input-----
The input consists of two integers:
• X: An integer representing the first value.
• Y: An integer representing the second value.

-----Output-----
The output is a pair (Int × Int) that:
• Contains the original Y as the first element.
• Contains the original X as the second element.

-----Note-----
There are no additional preconditions. The function simply swaps the two input values.
-/

@[reducible, simp]
def Swap_precond (X : Int) (Y : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def Swap_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : Swap_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem Swap_spec_satisfied (X: Int) (Y: Int) (h_precond : Swap_precond (X) (Y)) :
    Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
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
            "X": 1,
            "Y": 2
        },
        "expected": "(2, 1)",
        "unexpected": [
            "(1, 2)",
            "(2, 2)"
        ]
    },
    {
        "input": {
            "X": 0,
            "Y": 0
        },
        "expected": "(0, 0)",
        "unexpected": [
            "(0, 1)",
            "(1, 0)"
        ]
    },
    {
        "input": {
            "X": -1,
            "Y": 5
        },
        "expected": "(5, -1)",
        "unexpected": [
            "(-1, 5)",
            "(5, 5)"
        ]
    },
    {
        "input": {
            "X": 100,
            "Y": -100
        },
        "expected": "(-100, 100)",
        "unexpected": [
            "(100, -100)",
            "(-100, -100)"
        ]
    },
    {
        "input": {
            "X": 42,
            "Y": 42
        },
        "expected": "(42, 42)",
        "unexpected": [
            "(41, 42)",
            "(42, 41)"
        ]
    }
]
-/