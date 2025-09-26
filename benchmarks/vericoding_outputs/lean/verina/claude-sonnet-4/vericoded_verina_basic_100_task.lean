-- <vc-preamble>
import Mathlib

@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  3 * x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result

theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  unfold Triple_postcond
  unfold Triple
  constructor
  · -- Prove (3 * x) / 3 = x
    rw [Int.mul_ediv_cancel_left]
    norm_num
  · -- Prove (3 * x) / 3 * 3 = 3 * x
    rw [Int.mul_ediv_cancel_left]
    ring
    norm_num
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
        "expected": 0,
        "unexpected": [
            1,
            -1,
            10
        ]
    },
    {
        "input": {
            "x": 1
        },
        "expected": 3,
        "unexpected": [
            2,
            4,
            0
        ]
    },
    {
        "input": {
            "x": -2
        },
        "expected": -6,
        "unexpected": [
            -4,
            -2,
            6
        ]
    },
    {
        "input": {
            "x": 10
        },
        "expected": 30,
        "unexpected": [
            20,
            40,
            0
        ]
    },
    {
        "input": {
            "x": -5
        },
        "expected": -15,
        "unexpected": [
            -10,
            -5,
            15
        ]
    }
]
-/