-- <vc-preamble>
import Mathlib

@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result

theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 10
        },
        "expected": 30,
        "unexpected": [
            20,
            25,
            35
        ]
    },
    {
        "input": {
            "x": 18
        },
        "expected": 54,
        "unexpected": [
            50,
            56,
            60
        ]
    },
    {
        "input": {
            "x": 0
        },
        "expected": 0,
        "unexpected": [
            1,
            -1,
            5
        ]
    },
    {
        "input": {
            "x": -5
        },
        "expected": -15,
        "unexpected": [
            -10,
            -20,
            0
        ]
    },
    {
        "input": {
            "x": 25
        },
        "expected": 75,
        "unexpected": [
            70,
            80,
            65
        ]
    }
]
-/