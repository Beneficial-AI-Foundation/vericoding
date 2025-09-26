import Mathlib
-- <vc-preamble>
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this verification condition.
-- </vc-helpers>

-- <vc-definitions>
def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let y := 2 * x
(y, 2 * y)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  result.fst = 2 * x ∧ result.snd = 2 * result.fst

theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  simp [DoubleQuadruple_postcond, DoubleQuadruple]
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 0
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
            "x": 1
        },
        "expected": "(2, 4)",
        "unexpected": [
            "(2, 2)",
            "(1, 4)",
            "(3, 4)"
        ]
    },
    {
        "input": {
            "x": -1
        },
        "expected": "(-2, -4)",
        "unexpected": [
            "(-2, -2)",
            "(-1, -4)",
            "(-3, -4)"
        ]
    },
    {
        "input": {
            "x": 10
        },
        "expected": "(20, 40)",
        "unexpected": [
            "(20, 20)",
            "(10, 40)",
            "(20, 0)"
        ]
    },
    {
        "input": {
            "x": -5
        },
        "expected": "(-10, -20)",
        "unexpected": [
            "(-10, -10)",
            "(-5, -20)",
            "(-15, -20)"
        ]
    }
]
-/