-- <vc-preamble>
import Mathlib

@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  result = true ↔ ∃ k : Int, x = 2 * k

theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "x": 4
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": 7
        },
        "expected": false,
        "unexpected": [true]
    },
    {
        "input": {
            "x": 0
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -2
        },
        "expected": true,
        "unexpected": [false]
    },
    {
        "input": {
            "x": -3
        },
        "expected": false,
        "unexpected": [true]
    }
]
-/