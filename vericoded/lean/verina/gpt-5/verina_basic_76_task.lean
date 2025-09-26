import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if h : x ≤ y then x else y
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  (x ≤ y → result = x) ∧ (x > y → result = y)

theorem myMin_spec_satisfied (x: Int) (y: Int) (h_precond : myMin_precond (x) (y)) :
    myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
  unfold myMin_postcond
  constructor
  · intro hxy
    simp [myMin, hxy]
  · intro hgt
    have hnotle : ¬ x ≤ y := not_le_of_gt hgt
    simp [myMin, hnotle]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 3,
            "y": 5
        },
        "expected": 3,
        "unexpected": [
            5,
            8
        ]
    },
    {
        "input": {
            "x": 10,
            "y": 7
        },
        "expected": 7,
        "unexpected": [
            10,
            17
        ]
    },
    {
        "input": {
            "x": 4,
            "y": 4
        },
        "expected": 4,
        "unexpected": [
            0,
            8
        ]
    },
    {
        "input": {
            "x": -5,
            "y": 0
        },
        "expected": -5,
        "unexpected": [
            0,
            -4
        ]
    },
    {
        "input": {
            "x": 0,
            "y": -10
        },
        "expected": -10,
        "unexpected": [
            0,
            -8
        ]
    }
]
-/