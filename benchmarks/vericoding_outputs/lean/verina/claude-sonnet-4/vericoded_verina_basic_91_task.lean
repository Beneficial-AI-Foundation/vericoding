import Mathlib
-- <vc-preamble>
@[reducible, simp]
def Swap_precond (X : Int) (Y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple swap implementation
-- </vc-helpers>

-- <vc-definitions>
def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  (Y, X)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Swap_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : Swap_precond (X) (Y)) :=
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem Swap_spec_satisfied (X: Int) (Y: Int) (h_precond : Swap_precond (X) (Y)) :
    Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
  unfold Swap_postcond Swap
  constructor
  · rfl
  constructor
  · rfl
  · intro h_neq
    constructor
    · exact h_neq.symm
    · exact h_neq
-- </vc-theorems>

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