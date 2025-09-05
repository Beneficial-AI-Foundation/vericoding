/- 
-----Description-----
This task requires computing three times the given integer. The goal is to determine the product of the input integer and 3.

-----Input-----
The input consists of:
• x: An integer.

-----Output-----
The output is an integer that represents three times the input value.

-----Note-----
The implementation uses two different branches based on the value of x (i.e., x < 18 or x ≥ 18), but both branches guarantee that the result equals 3*x.
-/

import Mathlib

@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result

theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
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
