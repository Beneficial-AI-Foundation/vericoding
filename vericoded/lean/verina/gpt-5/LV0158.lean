import Mathlib
-- <vc-preamble>
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- no helper code needed
-- </vc-helpers>

-- <vc-definitions>
def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  (x + y, x - y)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) (h_precond : MultipleReturns_precond (x) (y)) :=
  result.1 = x + y ∧ result.2 + y = x

theorem MultipleReturns_spec_satisfied (x: Int) (y: Int) (h_precond : MultipleReturns_precond (x) (y)) :
    MultipleReturns_postcond (x) (y) (MultipleReturns (x) (y) h_precond) h_precond := by
  unfold MultipleReturns_postcond
  constructor
  · simp [MultipleReturns]
  · simpa [MultipleReturns] using sub_add_cancel x y
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 3,
            "y": 2
        },
        "expected": "(5, 1)",
        "unexpected": [
            "(6, 2)",
            "(5, 2)",
            "(4, 1)"
        ]
    },
    {
        "input": {
            "x": -2,
            "y": 3
        },
        "expected": "(1, -5)",
        "unexpected": [
            "(-1, 5)",
            "(2, -3)",
            "(1, 5)"
        ]
    },
    {
        "input": {
            "x": 0,
            "y": 0
        },
        "expected": "(0, 0)",
        "unexpected": [
            "(1, 0)",
            "(0, 1)",
            "(-1, 0)"
        ]
    },
    {
        "input": {
            "x": 10,
            "y": 5
        },
        "expected": "(15, 5)",
        "unexpected": [
            "(14, 5)",
            "(15, 6)",
            "(10, 5)"
        ]
    },
    {
        "input": {
            "x": -5,
            "y": -10
        },
        "expected": "(-15, 5)",
        "unexpected": [
            "(-15, -5)",
            "(-5, 15)",
            "(-10, 0)"
        ]
    }
]
-/