import Mathlib
-- <vc-preamble>
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple swap operation
-- </vc-helpers>

-- <vc-definitions>
def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  (Y, X)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem SwapSimultaneous_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
  unfold SwapSimultaneous_postcond
  unfold SwapSimultaneous
  simp
  intro h_neq
  constructor
  · exact Ne.symm h_neq
  · exact h_neq
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "X": 3,
            "Y": 4
        },
        "expected": "(4, 3)",
        "unexpected": [
            "(3, 4)",
            "(3, 3)"
        ]
    },
    {
        "input": {
            "X": -10,
            "Y": 20
        },
        "expected": "(20, -10)",
        "unexpected": [
            "(20, -20)",
            "(-10, 20)"
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
            "X": 123,
            "Y": -456
        },
        "expected": "(-456, 123)",
        "unexpected": [
            "(123, -456)",
            "(-123, 456)"
        ]
    },
    {
        "input": {
            "X": -1,
            "Y": -2
        },
        "expected": "(-2, -1)",
        "unexpected": [
            "(-1, -2)",
            "(-2, 2)"
        ]
    }
]
-/