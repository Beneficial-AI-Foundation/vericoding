import Mathlib
-- <vc-preamble>
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Helper definitions for arithmetic swap operations
-- </vc-helpers>

-- <vc-definitions>
def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  (Y, X)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)

theorem SwapArithmetic_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  unfold SwapArithmetic_postcond SwapArithmetic
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
            "X": 3,
            "Y": 4
        },
        "expected": "(4, 3)",
        "unexpected": [
            "(3, 4)",
            "(3, 3)",
            "(4, 4)"
        ]
    },
    {
        "input": {
            "X": -1,
            "Y": 10
        },
        "expected": "(10, -1)",
        "unexpected": [
            "(-1, 10)",
            "(10, 1)",
            "(-10, -1)"
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
            "(1, 0)",
            "(-1, 0)"
        ]
    },
    {
        "input": {
            "X": 100,
            "Y": 50
        },
        "expected": "(50, 100)",
        "unexpected": [
            "(100, 50)",
            "(50, 50)",
            "(100, 100)"
        ]
    },
    {
        "input": {
            "X": -5,
            "Y": -10
        },
        "expected": "(-10, -5)",
        "unexpected": [
            "(-5, -10)",
            "(-10, -10)",
            "(-5, -5)"
        ]
    }
]
-/